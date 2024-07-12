use seam;
use seam::assemble::MarkupFormatter;

use std::{io, env};
use std::path::PathBuf;
use std::error::Error;

use colored::*;

fn argument_fatal(msg: impl std::fmt::Display) -> ! {
    eprintln!("{} {}",
        format!("[{}]", "**".red()).white().bold(),
        msg.to_string().bold());
    std::process::exit(1)
}

const SUPPORTED_TARGETS: [&str; 5] = ["text", "sexp", "html", "xml", "css"];

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = env::args();
    let _ = args.next();  // Discard.

    let mut files = Vec::new();
    let mut target = String::from("");
    let mut from_stdin = false;
    let mut is_doc = true;

    for arg in args {
        if arg.chars().nth(0) == Some('-') {
            if let Some(opt) = arg.split("--").nth(1) {
                if SUPPORTED_TARGETS.contains(&opt) {
                    target = opt.to_owned();
                    continue;
                }
                match opt {
                   "nodocument" | "nodoc" => is_doc = false,
                   _ => argument_fatal(
                       format!("Unknown argument: `--{}'.", opt))
                }
            } else if let Some(opt) = arg.split("-").nth(1) {
                match opt {
                    "v" => {
                        let (major, minor, tiny) = seam::VERSION;
                        eprintln!("{}", format!("SEAM v{}.{}.{}",
                            major, minor, tiny).bold());
                        std::process::exit(0);
                    },
                    "" => {
                        from_stdin = true;
                    },
                    _ => argument_fatal(
                        format!("Unknown argument: `-{}'.", opt))
                }
            }
        } else {
            // Otherwise its a file path.
            let path = PathBuf::from(&arg);
            if path.exists() {
                files.push(path);
            } else {
                argument_fatal(format!("File not found: `{}'.", path.to_string_lossy()));
            }
        }
    }

    if files.is_empty() {
        from_stdin = true;
    }
    if target.is_empty() {
        argument_fatal("No such target format exists / \
                        no target format given.");
    }

    if from_stdin {
        let mut stdin = io::stdin();
        let builder = seam::tree_builder_stream(&mut stdin)?;
        generate_and_print(&builder, &target, is_doc);
    }

    for file in files {
        let builder = seam::tree_builder_file(&file)?;
        generate_and_print(&builder, &target, is_doc);
    }


    Ok(())
}

fn generate_and_print<'a>(expander: &'a seam::parse::expander::Expander<'a>, target: &str, is_doc: bool) {
    let tree = match expander.expand() {
        Ok(tree) => tree,
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    };
    let fmt: Box<dyn MarkupFormatter> = match target {
        "text" => Box::new(seam::assemble::text::PlainTextFormatter::new(tree)),
        "sexp" => Box::new(seam::assemble::sexp::SExpFormatter::new(tree)),
        "html" => Box::new(seam::assemble::html::HTMLFormatter::new(tree)),
        "xml"  => Box::new(seam::assemble::xml::XMLFormatter::new(tree)),
        "css"  => Box::new(seam::assemble::css::CSSFormatter::new(tree)),
        _ => {
            if SUPPORTED_TARGETS.contains(&target) {
                unreachable!("bug: target `{}' is not covered", target);
            }
            argument_fatal(
                format!("Target `{}', does not exist.", target))
        }
    };
    let result = if is_doc {
        fmt.document()
    } else {
        fmt.display()
    };

    match result {
        Ok(generated) => println!("{}", generated),
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1)
        }
    }
}
