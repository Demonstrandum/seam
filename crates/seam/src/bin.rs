use seam::assemble::MarkupFormatter;

use std::collections::{BTreeMap, BTreeSet};
use std::{io, env};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime};
use std::error::Error;

use colored::Colorize;

fn argument_fatal(msg: impl std::fmt::Display) -> ! {
    eprintln!("{} {}",
        format!("[{}]", "**".red()).white().bold(),
        msg.to_string().bold());
    std::process::exit(1)
}

const SUPPORTED_TARGETS: [&str; 7] = ["text", "sexp", "html", "xml", "css", "json", "js"];

const HELP: &str = "\
Usage: seam --<format> [options] [files...]
       seam run [options] [files...]

Expands each file (or STDIN, if none are given) and writes it in the given
format to STDOUT. `seam run' expands files only for what their macros do
(`%write', `%exec', `%log'), as build scripts, reporting it on STDOUT.

Formats:
  --html, --xml, --css, --js, --json, --sexp, --text

Options:
  -              Read from STDIN (as well as any files).
  -I<dir>        Also look for included and embedded files in <dir>.
  --nodoc        Write the output as it is, without making it a whole
                 document (e.g. no <!DOCTYPE html>, no indentation).
  --literate     Read the input as text with macros in it, rather than as
                 s-expressions.
  --watch, -w    Expand the files again whenever a file they read changes
                 (included, embedded, globbed, or a `%write' source).
  --version, -v  Print the version.
  --help, -h     Print this help.

See USAGE.md for the syntax and the built-in macros.";

struct Options {
    run: bool,
    target: String,
    include_dirs: BTreeSet<PathBuf>,
    is_doc: bool,
    literate: bool,
}

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
    let mut watch = false;

    for arg in args {
        if arg.starts_with('-') {
            if let Some(opt) = arg.strip_prefix("--") {
                if SUPPORTED_TARGETS.contains(&opt) {
                    opt.clone_into(&mut target);
                    continue;
                }
                match opt {
                   "nodocument" | "nodoc" => is_doc = false,
                   "literate" => literate = true,
                   "watch" => watch = true,
                   "version" => print_version(),
                   "help" => print_help(),
                   _ => argument_fatal(
                       format!("Unknown argument: `--{opt}' (see `seam --help')."))
                }
            } else if let Some(opt) = arg.strip_prefix('-') {
                match opt.as_bytes() {
                    [b'v'] => print_version(),
                    [b'h'] => print_help(),
                    [b'w'] => watch = true,
                    [b'I', ..] => {
                        let dir = &arg.as_str()[2..];
                        let dir = PathBuf::from(dir);
                        include_dirs.insert(dir);
                    },
                    [] => {
                        from_stdin = true;
                    },
                    _ => argument_fatal(
                        format!("Unknown argument: `-{opt}' (see `seam --help')."))
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
                        no target format given (see `seam --help').");
    }
    if watch && from_stdin {
        argument_fatal("`--watch' needs files to watch, rather than STDIN.");
    }

    let options = Options { run, target, include_dirs, is_doc, literate };

    if from_stdin {
        let mut stdin = io::stdin();
        let context = seam::Context::new();
        let builder = seam::tree_builder_stream(&context, &mut stdin, literate)?;
        builder.add_includes(options.include_dirs.iter());
        if let Err(error) = build(builder, &options) {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }

    if watch {
        watch_files(&files, &options);
    }

    let mut failed = false;
    for file in files {
        failed |= build_file(&file, &options).is_err();
    }
    if failed {
        std::process::exit(1);
    }
    Ok(())
}

fn print_version() -> ! {
    let (major, minor, tiny) = seam::VERSION;
    println!("{}", format!("SEAM v{major}.{minor}.{tiny}").bold());
    std::process::exit(0)
}

fn print_help() -> ! {
    println!("{HELP}");
    std::process::exit(0)
}

/// What a build was made from: the files read and the globs searched,
/// less the files it wrote itself.
#[derive(Default)]
struct Sources {
    files: BTreeSet<PathBuf>,
    globs: BTreeSet<String>,
    written: BTreeSet<PathBuf>,
}

impl Sources {
    fn extend(&mut self, context: &seam::Context) {
        self.files.extend(context.files_read());
        self.globs.extend(context.globs_searched());
        self.written.extend(context.files_written());
    }

    /// The modification time of each file, including every file the globs
    /// now match, so that new and deleted files are noticed too.
    fn snapshot(&self) -> BTreeMap<PathBuf, Option<SystemTime>> {
        let mut paths: BTreeSet<PathBuf> = self.files.clone();
        for pattern in &self.globs {
            if let Ok(matches) = glob::glob(pattern) {
                paths.extend(matches.flatten());
            }
        }
        paths.into_iter()
            .filter(|path| !self.written.contains(path))
            .map(|path| {
                let modified = std::fs::metadata(&path).and_then(|metadata| metadata.modified()).ok();
                (path, modified)
            })
            .collect()
    }
}

/// Build the files, then again each time something they were made from changes.
fn watch_files(files: &[PathBuf], options: &Options) -> ! {
    let status = |message: String| eprintln!("{} {}", format!("[{}]", "watch".cyan()).white().bold(), message);
    loop {
        let start = Instant::now();
        let mut sources = Sources::default();
        for file in files {
            sources.files.insert(file.clone());
            let context = seam::Context::new();
            // Errors are reported, and the files are watched for a fix.
            let _ = build_file_in(&context, file, options);
            sources.extend(&context);
        }
        let before = sources.snapshot();
        status(format!("Built in {:.0?}; watching {} files.", start.elapsed(), before.len()));

        // Poll until something changes.
        let changed = loop {
            std::thread::sleep(Duration::from_millis(250));
            let now = sources.snapshot();
            if now != before {
                let changed: Vec<&PathBuf> = before.keys().chain(now.keys())
                    .filter(|path| before.get(*path) != now.get(*path))
                    .collect::<BTreeSet<_>>().into_iter().collect();
                break changed.iter().map(|path| path.display().to_string()).collect::<Vec<_>>();
            }
        };
        status(format!("Changed: {}.", changed.join(", ")));
        // Let a burst of writes (e.g. an editor saving) finish first.
        std::thread::sleep(Duration::from_millis(50));
    }
}

fn build_file(file: &Path, options: &Options) -> Result<(), ()> {
    let context = seam::Context::new();
    build_file_in(&context, file, options)
}

fn build_file_in<'a>(context: &'a seam::Context<'a>, file: &Path, options: &Options) -> Result<(), ()> {
    let builder = match seam::tree_builder_file(context, file, options.literate) {
        Ok(builder) => builder,
        Err(error) => {
            eprintln!("{} Could not read `{}': {error}", format!("[{}]", "**".red()).white().bold(), file.display());
            return Err(());
        },
    };
    builder.add_includes(options.include_dirs.iter());
    build(builder, options).map_err(|error| eprintln!("{error}"))
}

/// Expand, and print the document (or, for `seam run`, only expand).
fn build(expander: seam::parse::expander::Expander, options: &Options) -> Result<(), String> {
    if options.run {
        expander.set_echo(true);
        return expander.expand().map(drop).map_err(|e| e.to_string());
    }
    let tree = expander.expand().map_err(|e| e.to_string())?;
    let fmt: Box<dyn MarkupFormatter> = match options.target.as_str() {
        "text" => Box::new(seam::assemble::text::PlainTextFormatter::new(tree)),
        "sexp" => Box::new(seam::assemble::sexp::SExpFormatter::new(tree)),
        "html" => Box::new(seam::assemble::html::HTMLFormatter::new(tree)),
        "xml"  => Box::new(seam::assemble::xml::XMLFormatter::new(tree)),
        "css"  => Box::new(seam::assemble::css::CSSFormatter::new(tree)),
        "json" => Box::new(seam::assemble::json::JSONFormatter::new(tree)),
        "js"   => Box::new(seam::assemble::js::JSFormatter::new(tree)),
        target => {
            if SUPPORTED_TARGETS.contains(&target) {
                unreachable!("bug: target `{}' is not covered", target);
            }
            argument_fatal(
                format!("Target `{target}', does not exist."))
        }
    };
    let generated = if options.is_doc { fmt.document() } else { fmt.display() };
    let generated = generated.map_err(|e| e.to_string())?;
    println!("{generated}");
    Ok(())
}
