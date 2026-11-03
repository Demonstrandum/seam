use seam::assemble::MarkupFormatter;

use std::collections::BTreeSet;
use std::{io, env};
use std::path::PathBuf;
use std::error::Error;

use colored::Colorize;

fn argument_fatal(msg: impl std::fmt::Display) -> ! {
    eprintln!("{} {}",
        format!("[{}]", "**".red()).white().bold(),
        msg.to_string().bold());
    std::process::exit(1)
}

const SUPPORTED_TARGETS: [&str; 5] = ["text", "sexp", "html", "xml", "css"];

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = env::args().peekable();
    let _ = args.next();  // Discard.

    // `seam run file.sex` expands a file only for its side effects
    // (`%write`, `%exec`, ...), which are reported on STDOUT instead.
    let run = args.next_if(|arg| arg == "run").is_some();

    // Command line flags and options.
    let mut files = Vec::new();
    let mut target = String::new();
    let mut include_dirs: BTreeSet<PathBuf> = BTreeSet::default();
    let mut from_stdin = false;
    let mut is_doc = true;
    let mut literate = false;

    for arg in args {
        if arg.starts_with('-') {
            if let Some(opt) = arg.split("--").nth(1) {
                if SUPPORTED_TARGETS.contains(&opt) {
                    opt.clone_into(&mut target);
                    continue;
                }
                match opt {
                   "nodocument" | "nodoc" => is_doc = false,
                   "literate" => literate = true,
                   _ => argument_fatal(
                       format!("Unknown argument: `--{opt}'."))
                }
            } else if let Some(opt) = arg.split('-').nth(1) {
                match opt.as_bytes() {
                    [b'v'] => {
                        let (major, minor, tiny) = seam::VERSION;
                        eprintln!("{}", format!("SEAM v{major}.{minor}.{tiny}").bold());
                        std::process::exit(0);
                    },
                    [b'I', ..] => {
                        let dir = &arg.as_str()[2..];
                        let dir = PathBuf::from(dir);
                        include_dirs.insert(dir);
                    },
                    [] => {
                        from_stdin = true;
                    },
                    _ => argument_fatal(
                        format!("Unknown argument: `-{opt}'."))
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
    if run {
        if !target.is_empty() {
            argument_fatal(format!("`seam run' takes no target format, but `--{target}' was given."));
        }
    } else if target.is_empty() {
        argument_fatal("No such target format exists / \
                        no target format given.");
    }

    if from_stdin {
        let mut stdin = io::stdin();
        let context = seam::Context::new();
        let builder = seam::tree_builder_stream(&context, &mut stdin, literate)?;
        builder.add_includes(include_dirs.iter());
        if run { execute(builder) } else { generate_and_print(builder, &target, is_doc) }
    }

    for file in files {
        let context = seam::Context::new();
        let builder = seam::tree_builder_file(&context, &file, literate)?;
        builder.add_includes(include_dirs.iter());
        if run { execute(builder) } else { generate_and_print(builder, &target, is_doc) }
    }

    Ok(())
}

/// Expand a file only for its side effects, discarding the document.
fn execute(expander: seam::parse::expander::Expander) {
    expander.set_echo(true);
    if let Err(e) = expander.expand() {
        eprintln!("{e}");
        std::process::exit(1);
    }
}

fn generate_and_print(expander: seam::parse::expander::Expander, target: &str, is_doc: bool) {
    let tree = match expander.expand() {
        Ok(tree) => tree,
        Err(e) => {
            eprintln!("{e}");
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
                format!("Target `{target}', does not exist."))
        }
    };
    let result = if is_doc {
        fmt.document()
    } else {
        fmt.display()
    };

    match result {
        Ok(generated) => println!("{generated}"),
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1)
        }
    }
}
