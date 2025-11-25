// klujur - A Clojure-ish interpreter written in Rust
// Copyright (c) 2025 Tom Waddington. MIT licensed.

use std::env;
use std::fs;
use std::io::{self, Write};
use std::path::Path;
use std::process;

use klujur_core::{
    Env, eval, init_stdlib, realize_for_print, register_builtins, set_bytecode_mode,
    set_bytecode_registry,
};
use klujur_parser::Parser;

fn main() {
    let args: Vec<String> = env::args().collect();

    // Handle --help flag
    if args.iter().any(|a| a == "--help" || a == "-h") {
        print_help();
        return;
    }

    // Handle --version flag
    if args.iter().any(|a| a == "--version" || a == "-v") {
        println!("Klujur v0.1.0");
        return;
    }

    // Check for --bytecode flag
    let bytecode_mode = args.iter().any(|a| a == "--bytecode" || a == "-b");
    if bytecode_mode {
        let _ = set_bytecode_mode(true);
    }

    // Filter out flags to get file arguments
    let files: Vec<&String> = args[1..].iter().filter(|a| !a.starts_with('-')).collect();

    // Create environment with builtins
    let env = Env::new();
    register_builtins(&env);

    // Load standard library macros
    if let Err(e) = init_stdlib(&env) {
        eprintln!("Failed to load stdlib: {}", e);
        process::exit(1);
    }

    // Set up bytecode registry for global resolution if bytecode mode is enabled
    if bytecode_mode {
        set_bytecode_registry(env.registry());
    }

    // If files provided, evaluate them; otherwise start REPL
    if !files.is_empty() {
        run_files(&files, &env);
    } else {
        run_repl(&env, bytecode_mode);
    }
}

fn print_help() {
    println!("Klujur v0.1.0 - A Clojure-ish interpreter");
    println!();
    println!("Usage: klujur [OPTIONS] [FILES...]");
    println!();
    println!("Options:");
    println!("  -b, --bytecode  Enable bytecode compilation mode");
    println!("  -v, --version   Print version information");
    println!("  -h, --help      Print this help message");
    println!();
    println!("If no files are provided, starts an interactive REPL.");
}

/// Evaluate a sequence of source files
fn run_files(files: &[&String], env: &Env) {
    for file_path in files {
        if let Err(e) = eval_file(file_path, env) {
            eprintln!("{}", e);
            process::exit(1);
        }
    }
}

/// Evaluate a single source file
fn eval_file(file_path: &str, env: &Env) -> Result<(), String> {
    let path = Path::new(file_path);

    // Validate file extension
    match path.extension().and_then(|e| e.to_str()) {
        Some("klj") | Some("cljc") => {}
        Some(ext) => {
            return Err(format!(
                "Error: unsupported file extension '.{}' for '{}'",
                ext, file_path
            ));
        }
        None => {
            return Err(format!(
                "Error: file '{}' has no extension (expected .klj or .cljc)",
                file_path
            ));
        }
    }

    // Read and evaluate the file
    let source =
        fs::read_to_string(path).map_err(|e| format!("Error reading '{}': {}", file_path, e))?;

    let mut parser =
        Parser::new(&source).map_err(|e| format!("Lexer error in '{}': {:?}", file_path, e))?;

    // Evaluate all expressions in the file
    loop {
        match parser.parse() {
            Ok(Some(expr)) => {
                eval(&expr, env).map_err(|e| format!("Error in '{}': {}", file_path, e))?;
            }
            Ok(None) => break,
            Err(e) => return Err(format!("Parse error in '{}': {:?}", file_path, e)),
        }
    }

    Ok(())
}

/// Run the interactive REPL
fn run_repl(env: &Env, bytecode_mode: bool) {
    if bytecode_mode {
        println!("Klujur v0.1.0 (bytecode mode)");
    } else {
        println!("Klujur v0.1.0");
    }

    loop {
        // Display current namespace in prompt
        let ns_name = env.registry().current_name();
        print!("{}=> ", ns_name);
        io::stdout().flush().unwrap();

        let mut input = String::new();
        match io::stdin().read_line(&mut input) {
            Ok(0) => {
                println!();
                break;
            }
            Ok(_) => {
                let input = input.trim();
                if input.is_empty() {
                    continue;
                }

                match Parser::new(input) {
                    Ok(mut parser) => match parser.parse() {
                        Ok(Some(expr)) => match eval(&expr, env) {
                            Ok(result) => match realize_for_print(result) {
                                Ok(realized) => println!("{}", realized),
                                Err(e) => eprintln!("Error realizing result: {}", e),
                            },
                            Err(e) => eprintln!("Error: {}", e),
                        },
                        Ok(None) => {}
                        Err(e) => eprintln!("Parse error: {:?}", e),
                    },
                    Err(e) => eprintln!("Lexer error: {:?}", e),
                }
            }
            Err(e) => {
                eprintln!("Read error: {}", e);
                break;
            }
        }
    }
}
