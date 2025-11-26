#?(:klj (require '[klujur.math :as Math]))

#?(:clj (require '[clojure.string :as s])
   :klj (require '[klujur.string :as s]))

(defn set-bit
  "Sets or clears bit i in num.

  If value is truthy, sets the bit to 1.
  If value is falsy, clears the bit to 0.

  Example:
    (set-bit 0 3 true)  => 8
    (set-bit 15 0 false) => 14"
  [num i value]
  (if value
    (bit-or num (bit-shift-left 1 i))
    (bit-and num (bit-not (bit-shift-left 1 i)))))

(defn idiv
  "Integer division (floor division).

  Returns the floor of a divided by b.

  Example:
    (idiv 7 2)  => 3
    (idiv -7 2) => -4"
  [a b]
  #?(:clj (long (Math/floor (/ a b)))
     :klj (int (Math/floor (/ a b)))))

;; Constants
(def ^:private braille-offset 0x2800)

;; Core Functions

(defn braille
  "Converts a byte (0-255) to a braille Unicode character.

  Each bit in the byte corresponds to one of the 8 dots in a braille character.
  The byte is added to the braille Unicode offset (0x2800) to get the final character.

  Example:
    (braille 0)   => \"⠀\"  ; blank
    (braille 255) => \"⣿\"  ; all dots filled"
  [byte-val]
  (str (char (+ braille-offset byte-val))))

(defn bit-of-subpixel
  "Maps a subpixel coordinate [x y] to its corresponding bit position (0-7).

  The mapping follows the braille standard layout:
  - x is 0-1 (left or right column)
  - y is 0-3 (top to bottom)

  The bit layout is:
    [0,0]=0  [1,0]=3
    [0,1]=1  [1,1]=4
    [0,2]=2  [1,2]=5
    [0,3]=6  [1,3]=7

  Example:
    (bit-of-subpixel [0 0]) => 0
    (bit-of-subpixel [1 3]) => 7"
  [[x y]]
  (if (= y 3) (+ 6 x) (+ (* 3 x) y)))

(defn set-subpixel
  "Sets or clears a specific subpixel in a byte value.

  Returns a new byte with the specified subpixel bit set or cleared.

  Example:
    (set-subpixel 0 [0 0] true)  => 1
    (set-subpixel 255 [0 0] false) => 254"
  [num subpixel value]
  (set-bit num (bit-of-subpixel subpixel) value))

(defn new-canvas
  "Creates a new canvas with the specified width and height in 'pixels'.

  Each pixel is a braille character representing a 2x4 grid of subpixels.
  So a 10x5 canvas has dimensions of 20x20 in subpixel coordinates.

  Example:
    (new-canvas 10 5)
    => {:width 10, :height 5, :pixels [0 0 0 ...]}"
  [width height]
  {:width width :height height :pixels (vec (repeat (* width height) 0))})

(defn bounds
  "Returns the canvas dimensions in subpixels [width height].

  Since each pixel is 2x4 subpixels, the subpixel dimensions are:
  - width * 2
  - height * 4

  Example:
    (bounds (new-canvas 10 5)) => [20 20]"
  [{:keys [width height]}]
  [(* 2 width) (* 4 height)])

(defn draw-point
  "Draws a point at subpixel coordinates [x y] on the canvas.

  Returns a new canvas with the point drawn. Coordinates are rounded to
  nearest integer. Points outside canvas bounds are silently ignored.

  The optional value parameter determines whether to set (true) or clear (false)
  the point. Defaults to true.

  Example:
    (-> (new-canvas 10 5)
        (draw-point [10 10])
        (draw-point [5 5] false))  ; clear a point"
  ([canvas point] (draw-point canvas point true))
  ([canvas [x y] value]
   (let [{:keys [width height _]} canvas
         x       (Math/round (double x))
         y       (Math/round (double y))
         pixel-x (idiv x 2)
         pixel-y (idiv y 4)]
     (if (or (< pixel-x 0) (< pixel-y 0) (>= pixel-x width) (>= pixel-y height))
       canvas ; out of bounds, return unchanged
       (let [pixel-ix (+ (* pixel-y width) pixel-x)
             subpixel [(mod x 2) (mod y 4)]]
         (update
          canvas
          :pixels
          (fn [pixels]
            (update pixels pixel-ix #(set-subpixel % subpixel value)))))))))

(defn canvas->string
  "Converts a canvas to a string representation using braille characters.

  Returns a multi-line string where each line represents one row of the canvas.

  Example:
    (-> (new-canvas 5 3)
        (draw-point [5 6])
        (canvas->string))
    => \"⠀⠀⡀⠀⠀\\n⠀⠀⠀⠀⠀\\n⠀⠀⠀⠀⠀\""
  [{:keys [width height pixels]}]
  (apply str
         (for [y (range height)]
           (str (apply str
                       (for [x    (range width)
                             :let [i (+ (* y width) x)]]
                         (braille (nth pixels i))))
                (when (< y (dec height)) "\n")))))

(defn print-canvas!
  "Prints a canvas to stdout using braille characters.

  Side-effecting function that prints the canvas and returns nil.

  NOTE: This function outputs line-by-line to avoid nREPL's 1024-byte
  buffer boundary issue which can corrupt UTF-8 multibyte sequences.

  Example:
    (-> (new-canvas 10 5)
        (draw-line [0 0] [20 20])
        (print-canvas!))"
  [canvas]
  (let [s     (canvas->string canvas)
        lines (s/split s #"\n")]
    (doseq [line lines]
      (println line)))
  nil)

;; Vector operations

(defn- span
  "Calculates the span between two points along an axis (0=x, 1=y)."
  [axis p0 p1]
  (- (nth p1 axis) (nth p0 axis)))

(defn- sign
  "Returns the sign of a number: -1, 0, or 1."
  [x]
  (cond (< x 0) -1
        (> x 0) 1
        :else 0))

(defn- make-vec2
  "Constructs a 2D vector from major/minor axis values.
  major-axis is 0 for x, 1 for y."
  [major-axis major minor]
  (case major-axis
    0 [major minor]
    1 [minor major]))

(defn draw-line
  "Draws a line from start point to end point using Bresenham's algorithm.

  Returns a new canvas with the line drawn. Both start and end are subpixel
  coordinates.

  Example:
    (-> (new-canvas 10 5)
        (draw-line [0 0] [20 20])
        (draw-line [0 20] [20 0]))"
  [canvas start end]
  (let [x-axis      0
        y-axis      1
        x-span      (span x-axis start end)
        y-span      (span y-axis start end)
        ;; Determine major and minor axes
        [major-axis minor-axis] (if (< (Math/abs y-span) (Math/abs x-span))
                                  [x-axis y-axis]
                                  [y-axis x-axis])
        ;; Ensure we draw from lower to higher major coordinate
        [start end] (if (< (nth start major-axis) (nth end major-axis))
                      [start end]
                      [end start])
        minor-step  (sign (- (nth end minor-axis) (nth start minor-axis)))
        run         (- (nth end major-axis) (nth start major-axis))
        rise        (Math/abs (- (nth end minor-axis) (nth start minor-axis)))]
    ;; Bresenham's algorithm using loop/recur
    (loop [canvas canvas
           major  (nth start major-axis)
           minor  (nth start minor-axis)
           err    (- (* 2 rise) run)]
      (if (> major (nth end major-axis))
        canvas
        (let [canvas      (draw-point canvas (make-vec2 major-axis major minor))
              [minor err] (if (> err 0)
                            [(+ minor minor-step) (- err (* 2 run))]
                            [minor err])]
          (recur canvas (inc major) minor (+ err (* 2 rise))))))))

(defn plot->string
  "Plots a mathematical function and returns the string representation.

  Arguments:
  - f: Function to plot (takes a number, returns a number)
  - [w h]: Canvas dimensions in pixels
  - x-scale: The range of x values (from -x-scale to +x-scale)
  - y-scale: The range of y values (from -y-scale to +y-scale)

  Options:
  - :axis - Whether to draw x and y axes (default: true)

  The function is sampled at regular intervals across the canvas width,
  and consecutive points are connected with lines.

  Returns the canvas as a string using braille characters.

  Example:
    (plot->string #(Math/sin %) [40 10] Math/PI 1)
    (plot->string #(Math/cos %) [20 10] Math/PI 1 :axis false)"
  [f [w h] x-scale y-scale & {:keys [axis] :or {axis true}}]
  (let [canvas  (new-canvas w h)
        [w h]   (bounds canvas)
        canvas  (if axis
                  ;; Draw axes
                  (let [canvas (reduce (fn [c i] (draw-point c [(/ w 2) i]))
                                       canvas
                                       (range h))]
                    (reduce (fn [c i] (draw-point c [i (/ h 2)]))
                            canvas
                            (range w)))
                  canvas)
        ;; Narrow y range slightly to avoid clipping extremes
        y-scale (* y-scale (/ (inc h) h))]
    ;; Sample function and draw lines between consecutive points
    (loop [i          0
           prev-point nil
           canvas     canvas]
      (if (>= i w)
        (canvas->string canvas)
        (let [;; x spans -0.5 to 0.5 (inclusive)
              x      (- (/ i (dec w)) 0.5)
              y      (/ (f (* x 2 x-scale)) y-scale -2)
              p      [(* (+ x 0.5) (dec w)) (* (+ y 0.5) h)]
              canvas (if prev-point (draw-line canvas prev-point p) canvas)]
          (recur (inc i) p canvas))))))

(defn print-plot!
  "Plots a mathematical function on a new canvas and prints it.

  Arguments:
  - f: Function to plot (takes a number, returns a number)
  - [w h]: Canvas dimensions in pixels
  - x-scale: The range of x values (from -x-scale to +x-scale)
  - y-scale: The range of y values (from -y-scale to +y-scale)

  Options:
  - :axis - Whether to draw x and y axes (default: true)

  The function is sampled at regular intervals across the canvas width,
  and consecutive points are connected with lines.

  Example:
    (print-plot! #(Math/sin %) [40 10] Math/PI 1)
    (print-plot! #(Math/cos %) [20 10] Math/PI 1 :axis false)"
  [f [w h] x-scale y-scale & {:keys [axis] :or {axis true}}]
  (let [s     (plot->string f [w h] x-scale y-scale :axis axis)
        lines (s/split s #"\n")]
    (doseq [line lines]
      (println line))
    nil))

(defn golden-spiral
  "Draw the golden spiral on a canvas."
  [canvas center scale max-θ start-angle]
  (let [φ       1.618033988749895
        [cx cy] center
        steps   1000]
    (loop [i          0
           prev-point nil
           canvas     canvas]
      (if (>= i steps)
        canvas
        (let [θ      (+ start-angle (* max-θ (/ i (dec steps))))
              r      (* scale (Math/pow φ (/ θ (/ Math/PI 2))))
              x      (+ cx (* r (Math/cos (- θ))))
              y      (+ cy (* r (Math/sin (- θ))))
              point  [(int x) (int y)]
              canvas (if prev-point (draw-line canvas prev-point point) canvas)]
          (recur (inc i) point canvas))))))

(-> (new-canvas 60 20)
    (golden-spiral [60 45] 0.5 (* 6 Math/PI) (* 0.75 Math/PI))
    (print-canvas!))
