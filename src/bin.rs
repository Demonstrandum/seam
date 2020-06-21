use seam;
use seam::assemble::Documentise;

use std::env;
use std::path::PathBuf;
use std::error::Error;

use colored::*;

fn argument_fatal(msg : &str) -> ! {
    eprintln!("{} {}",
        format!("[{}]", "**".red()).white().bold(),
        msg.bold());
    std::process::exit(1)
}

const SUPPORTED_TARGETS : [&str; 1] = ["html"];

fn main() -> Result<(), Box<dyn Error>> {
    let (major, minor, tiny) = seam::VERSION;
    eprintln!("{}", format!("SEAM v{}.{}.{}",
        major, minor, tiny).bold());

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
        }
        let path = PathBuf::from(&arg);
        if path.exists() {
            eprintln!("Reading file `{}'.", &path.display());
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
        let tree = seam::parse_file(&file)?;
        /*eprintln!("{}", &tree
            .iter().fold(String::new(),
            |acc, s| acc + "\n" + &s.to_string()));*/
        if target == "html" {
            let fmt = seam::assemble::html::HTMLFormatter::new(tree);
            let result = fmt.document();
            println!("{}", result);
        }
    }

    eprintln!("All files read and converted.");

    Ok(())
}
