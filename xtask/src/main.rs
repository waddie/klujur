// xtask - Build automation for klujur
// Copyright (c) 2025 Tom Waddington. MIT licensed.

use std::env;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::{Command, exit};

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();

    match args.first().map(String::as_str) {
        Some("install") => install(&args[1..]),
        Some("uninstall") => uninstall(&args[1..]),
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
    help                        Show this message
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
