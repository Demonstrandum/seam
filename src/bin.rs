use seam;
use seam::assemble::MarkupDisplay;

use std::env;
use std::path::PathBuf;
use std::error::Error;

use colored::*;

fn argument_fatal(msg : impl std::fmt::Display) -> ! {
    eprintln!("{} {}",
        format!("[{}]", "**".red()).white().bold(),
        msg.to_string().bold());
    std::process::exit(1)
}

const SUPPORTED_TARGETS : [&str; 2] = ["html", "xml"];

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = env::args();
    args.next();  // Discard.

    let mut files = Vec::new();
    let mut target = "";

    for arg in args {
        if let Some(opt) = arg.split("--").nth(1) {
            if SUPPORTED_TARGETS.contains(&opt) {
                target = Box::leak(opt.to_owned().into_boxed_str());
            }
            continue;
        } else if let Some(opt) = arg.split("-").nth(1) {
            match opt {
                "v" => {
                    let (major, minor, tiny) = seam::VERSION;
                    eprintln!("{}", format!("SEAM v{}.{}.{}",
                        major, minor, tiny).bold());
                    std::process::exit(0);
                },
                _ => argument_fatal(
                    format!("Unknown argument (`-{}').", opt))
            }
        }
        let path = PathBuf::from(&arg);
        if path.exists() {
            files.push(path);
        }
    }

    if files.is_empty() {
        argument_fatal("No input files given.");
    }
    if target.is_empty() {
        argument_fatal("No such target exists / no target given.");
    }

    for file in files {
        let tree = match seam::parse_file(&file) {
            Ok(tree) => tree,
            Err(e) => {
                eprintln!("{}", e);
                std::process::exit(1)
            }
        };
        #[cfg(feature="debug")]
        eprintln!("{}", &tree
            .iter().fold(String::new(),
            |acc, s| acc + "\n" + &s.to_string()));
        let result = match target {
            "html" => {
                let fmt = seam::assemble::html::HTMLFormatter::new(tree);
                fmt.document()
            },
            "xml"  => {
                let fmt = seam::assemble::xml::XMLFormatter::new(tree);
                fmt.document()
            },
            _ => {
                argument_fatal(
                    format!("Target `{}', does not exist.", target))
            }
        };
        match result {
            Ok(generated) => print!("{}", generated),
            Err(e) => {
                eprintln!("{}", e);
                std::process::exit(1)
            }
        }
    }


    Ok(())
}
