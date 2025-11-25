// xtask - Build automation for klujur
// Copyright (c) 2025 Tom Waddington. MIT licensed.

use std::env;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::{Command, Stdio, exit};

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();

    match args.first().map(String::as_str) {
        Some("install") => install(&args[1..]),
        Some("uninstall") => uninstall(&args[1..]),
        Some("test") => test(&args[1..]),
        Some("help") | Some("-h") | Some("--help") | None => help(),
        Some(cmd) => {
            eprintln!("Unknown command: {}", cmd);
            help();
            exit(1);
        }
    }
}

fn help() {
    println!(
        r#"klujur xtask - Build automation

USAGE:
    cargo xtask <COMMAND>

COMMANDS:
    install [--prefix <PATH>]   Build release and install to ~/.cargo/bin (or PREFIX/bin)
    uninstall [--prefix <PATH>] Remove installed files
    test [OPTIONS] [PATTERN]    Run klujur.test suite
    help                        Show this message

TEST OPTIONS:
    --release       Run tests with release build
    --verbose, -v   Show detailed output for each test
    --summary       Show only the summary (default)
    --failing       Show only failing tests
    PATTERN         Filter tests by filename pattern (e.g., "atoms" or "seq")

EXAMPLES:
    cargo xtask test              Run all tests
    cargo xtask test atoms        Run tests matching "atoms"
    cargo xtask test --verbose    Run all tests with detailed output
    cargo xtask test --release    Run tests with release build
"#
    );
}

fn get_bin_dir(args: &[String]) -> PathBuf {
    let prefix = if let Some(pos) = args.iter().position(|a| a == "--prefix") {
        args.get(pos + 1).map(PathBuf::from).unwrap_or_else(|| {
            eprintln!("--prefix requires a path argument");
            exit(1);
        })
    } else {
        dirs_home().join(".cargo")
    };
    prefix.join("bin")
}

fn dirs_home() -> PathBuf {
    env::var("HOME").map(PathBuf::from).unwrap_or_else(|_| {
        eprintln!("Could not determine home directory");
        exit(1);
    })
}

fn project_root() -> PathBuf {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest_dir).parent().unwrap().to_path_buf()
}

fn install(args: &[String]) {
    let bin_dir = get_bin_dir(args);
    let root = project_root();

    println!("Building release...");
    let status = Command::new("cargo")
        .args(["build", "--release"])
        .current_dir(&root)
        .status()
        .expect("Failed to run cargo build");

    if !status.success() {
        eprintln!("Build failed");
        exit(1);
    }

    fs::create_dir_all(&bin_dir).expect("Failed to create bin directory");

    // Install klujur binary
    let src_binary = root.join("target/release/klujur");
    let dst_binary = bin_dir.join("klujur");
    println!(
        "Installing {} -> {}",
        src_binary.display(),
        dst_binary.display()
    );
    fs::copy(&src_binary, &dst_binary).expect("Failed to copy klujur binary");
    fs::set_permissions(&dst_binary, fs::Permissions::from_mode(0o755))
        .expect("Failed to set permissions");

    // Install klj script with updated bin_dir
    let klj_template = root.join("script/klj");
    let klj_content = fs::read_to_string(&klj_template).expect("Failed to read klj script");
    let klj_updated = klj_content
        .lines()
        .map(|line| {
            if line.starts_with("bin_dir=") {
                format!("bin_dir=\"{}\"", bin_dir.display())
            } else {
                line.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");

    let dst_klj = bin_dir.join("klj");
    println!(
        "Installing {} -> {}",
        klj_template.display(),
        dst_klj.display()
    );
    fs::write(&dst_klj, klj_updated + "\n").expect("Failed to write klj script");
    fs::set_permissions(&dst_klj, fs::Permissions::from_mode(0o755))
        .expect("Failed to set permissions");

    println!("\nInstalled klujur and klj to {}", bin_dir.display());
    println!("Ensure {} is in your PATH", bin_dir.display());
}

fn uninstall(args: &[String]) {
    let bin_dir = get_bin_dir(args);

    let klujur = bin_dir.join("klujur");
    let klj = bin_dir.join("klj");

    for path in [&klujur, &klj] {
        if path.exists() {
            println!("Removing {}", path.display());
            fs::remove_file(path).expect("Failed to remove file");
        }
    }

    println!("Uninstalled klujur and klj from {}", bin_dir.display());
}

// =============================================================================
// Test Command
// =============================================================================

#[derive(Debug)]
struct TestResult {
    name: String,
    assertions: u32,
    passed: u32,
    failed: u32,
    errors: u32,
    #[allow(dead_code)]
    output: String, // Stored for potential future use (e.g., verbose error reporting)
}

impl TestResult {
    fn is_perfect(&self) -> bool {
        self.failed == 0 && self.errors == 0
    }

    fn pass_rate(&self) -> f64 {
        if self.assertions == 0 {
            0.0
        } else {
            (self.passed as f64 / self.assertions as f64) * 100.0
        }
    }
}

fn test(args: &[String]) {
    let root = project_root();
    let test_dir = root.join("test/klujur");

    // Parse arguments
    let release = args.iter().any(|a| a == "--release");
    let verbose = args.iter().any(|a| a == "--verbose" || a == "-v");
    let failing_only = args.iter().any(|a| a == "--failing");
    let pattern: Option<&str> = args
        .iter()
        .find(|a| !a.starts_with('-'))
        .map(String::as_str);

    // Build first
    println!(
        "Building klujur{}...",
        if release { " (release)" } else { "" }
    );
    let build_args = if release {
        vec!["build", "--release", "--quiet"]
    } else {
        vec!["build", "--quiet"]
    };

    let status = Command::new("cargo")
        .args(&build_args)
        .current_dir(&root)
        .status()
        .expect("Failed to run cargo build");

    if !status.success() {
        eprintln!("Build failed");
        exit(1);
    }

    // Find test files
    let binary = if release {
        root.join("target/release/klujur")
    } else {
        root.join("target/debug/klujur")
    };

    let mut test_files: Vec<PathBuf> = fs::read_dir(&test_dir)
        .expect("Failed to read test directory")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| {
            p.extension().is_some_and(|e| e == "cljc")
                && p.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.ends_with("_test.cljc"))
        })
        .filter(|p| {
            if let Some(pat) = pattern {
                p.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.contains(pat))
            } else {
                true
            }
        })
        .collect();

    test_files.sort();

    if test_files.is_empty() {
        if let Some(pat) = pattern {
            eprintln!("No test files matching pattern: {}", pat);
        } else {
            eprintln!("No test files found in {}", test_dir.display());
        }
        exit(1);
    }

    println!(
        "\nRunning {} test file{}...\n",
        test_files.len(),
        if test_files.len() == 1 { "" } else { "s" }
    );

    // Run tests
    let mut results: Vec<TestResult> = Vec::new();

    for test_file in &test_files {
        let name = test_file
            .file_stem()
            .and_then(|n| n.to_str())
            .unwrap_or("unknown")
            .to_string();

        if verbose {
            println!("=== {} ===", name);
        }

        let output = Command::new(&binary)
            .arg(test_file)
            .current_dir(&root)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .expect("Failed to run test");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let full_output = format!("{}{}", stdout, stderr);

        // Parse results from output
        let result = parse_test_output(&name, &full_output);

        if verbose {
            println!("{}", full_output.trim());
            println!();
        } else if !result.is_perfect() && !failing_only {
            // Show a brief indicator for imperfect tests
            print!(".");
        } else if result.is_perfect() && !failing_only {
            print!(".");
        }

        results.push(result);
    }

    if !verbose {
        println!();
    }

    // Print summary
    print_test_summary(&results, failing_only);
}

fn parse_test_output(name: &str, output: &str) -> TestResult {
    // Look for "Ran N assertions."
    // Look for "N passed, N failed, N errors."
    let mut assertions = 0u32;
    let mut passed = 0u32;
    let mut failed = 0u32;
    let mut errors = 0u32;

    for line in output.lines() {
        if line.starts_with("Ran ")
            && line.contains("assertion")
            && let Some(n) = line
                .strip_prefix("Ran ")
                .and_then(|s| s.split_whitespace().next())
                .and_then(|s| s.parse().ok())
        {
            assertions = n;
        }

        if line.contains("passed") && line.contains("failed") {
            // Parse "N passed, N failed, N errors."
            let parts: Vec<&str> = line.split(',').collect();
            for part in parts {
                let part = part.trim();
                if part.contains("passed") {
                    if let Some(n) = part.split_whitespace().next().and_then(|s| s.parse().ok()) {
                        passed = n;
                    }
                } else if part.contains("failed") {
                    if let Some(n) = part.split_whitespace().next().and_then(|s| s.parse().ok()) {
                        failed = n;
                    }
                } else if part.contains("error")
                    && let Some(n) = part.split_whitespace().next().and_then(|s| s.parse().ok())
                {
                    errors = n;
                }
            }
        }

        // Check for parse errors
        if line.contains("Parse error") || line.contains("ParseError") {
            errors = errors.max(1);
            if assertions == 0 {
                assertions = 1; // Count it as one failed assertion
            }
        }
    }

    TestResult {
        name: name.to_string(),
        assertions,
        passed,
        failed,
        errors,
        output: output.to_string(),
    }
}

fn print_test_summary(results: &[TestResult], failing_only: bool) {
    let total_assertions: u32 = results.iter().map(|r| r.assertions).sum();
    let total_passed: u32 = results.iter().map(|r| r.passed).sum();
    let total_failed: u32 = results.iter().map(|r| r.failed).sum();
    let total_errors: u32 = results.iter().map(|r| r.errors).sum();

    let perfect_count = results.iter().filter(|r| r.is_perfect()).count();
    let imperfect: Vec<&TestResult> = results.iter().filter(|r| !r.is_perfect()).collect();

    println!("\n{}", "=".repeat(70));
    println!("TEST SUMMARY");
    println!("{}", "=".repeat(70));

    // Show perfect tests
    if !failing_only && perfect_count > 0 {
        println!("\n100% Pass Rate ({} tests):", perfect_count);
        for result in results.iter().filter(|r| r.is_perfect()) {
            println!(
                "  ✓ {} - {}/{} assertions",
                result.name, result.passed, result.assertions
            );
        }
    }

    // Show imperfect tests
    if !imperfect.is_empty() {
        println!("\nTests with failures ({} tests):", imperfect.len());

        // Sort by pass rate (lowest first)
        let mut sorted: Vec<&&TestResult> = imperfect.iter().collect();
        sorted.sort_by(|a, b| a.pass_rate().partial_cmp(&b.pass_rate()).unwrap());

        for result in sorted {
            let indicator = if result.pass_rate() >= 90.0 {
                "○"
            } else if result.pass_rate() >= 70.0 {
                "△"
            } else {
                "✗"
            };

            println!(
                "  {} {} - {}/{} ({:.1}%) [{}F {}E]",
                indicator,
                result.name,
                result.passed,
                result.assertions,
                result.pass_rate(),
                result.failed,
                result.errors
            );
        }
    }

    // Overall summary
    let overall_rate = if total_assertions > 0 {
        (total_passed as f64 / total_assertions as f64) * 100.0
    } else {
        0.0
    };

    println!("\n{}", "-".repeat(70));
    println!(
        "TOTAL: {}/{} assertions ({:.1}%)",
        total_passed, total_assertions, overall_rate
    );
    println!(
        "       {} passed, {} failed, {} errors across {} test files",
        total_passed,
        total_failed,
        total_errors,
        results.len()
    );
    println!(
        "       {} tests at 100%, {} tests with failures",
        perfect_count,
        imperfect.len()
    );
    println!("{}", "=".repeat(70));

    // Exit with error if any failures
    if total_failed > 0 || total_errors > 0 {
        exit(1);
    }
}
