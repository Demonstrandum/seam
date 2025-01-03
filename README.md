# SEAM

> **S**ymbolic **E**xpressions **A**s **M**arkup.

## Why

Because all markup is terrible, especially XML/SGML and derivatives.

But mainly, for easier static markup code generation, such as by
macros and code includes and such.

## Try it out

This may be used as a Rust library, such as from within a server,
generating HTML (or any other supported markup) before it is served to the
client.  Personally, I just use the `seam` binary to statically
generate my personal websites through a Makefile.

Read the [USAGE.md](USAGE.md) file for code examples and documentation.

### Current Formats

 - XML (`--xml`; including: SVG, MathML)
 - HTML (`--html`; SGML)
 - CSS (`--css`)
 - SExp (`--sexp`; S-expression, basically a macro expansion utility)
 - Plain Text (`--text`; renders escaped strings to text)

### Installation

You may clone the repo, then build and install by
```sh
git clone git://git.knutsen.co/seam
cd seam
cargo build --release
cargo install --path .
```

Or install it from [crates.io](https://crates.io/crates/seam)
```sh
cargo install seam
```

Either way, you'll need the Rust (nightly) compiler and along
with it, comes `cargo`.

### Using The Binary

You may use it by passing in a file and piping from STDOUT.
```sh
seam test.sex --html > test.html
```

`test.sex` contains your symbolic-expressions, which is used to generate
HTML, saved in `test.html`.

Likewise, you may read from STDIN
```sh
seam --html < example.sex > example.html
# ... same as
cat example.sex | seam --html > example.html
```
You may also use here-strings or here-docs, if your shell
supports it.
```sh
seam --html <<< "(p Hello World)"
#stdout:
#   <!DOCTYPE html>
#   <html>
#   <head></head>
#   <body>
#   <p>Hello World</p>
#   </body>
#   </html>
```
```sh
seam --html --nodocument <<< "(p Hello World)"
#stdout:
#   <p>Hello World</p>
```
```sh
seam --xml <<< '(para Today is a day in (%date "%B, year %Y").)'
#stdout:
#   <?xml version="1.0" encoding="UTF-8" ?>
#   <para>Today is a day in November, year 2020.</para>
```
```sh
seam --sexp <<< '(hello (%define subject world) %subject)'
#stdout:
#   (hello world)
```

## Checklist
 - [ ] Literate mode for parser+lexer, where string nodes are not escaped and parentheses are converted to symbols.
       The only time strings are escaped and parentheses make lists is inside a `(%` and `)` pair, i.e. when calling a macro.
       So `hello world (earth) (%do (p letter "\x61")) "\x61"` turns in to (in HTML mode)
       `hello world <earth></earth> <p>hi a</p> a` normally, but in *literate* (HTML) mode turns into
       `hello world (earth) <p>letter a</p> "\x61"`. Parentheses and quotes have been preserved.
       Markdown source in `(%markdown ...)` should be parsed as literate files by default.
       Provide command line `--literate` option; `%include` and `%embed` should also have options for enabling literate mode.
 - [ ] Way to match on unknown keywords in attributes, examples when `(%define dict (:a 1 :b 2 :c 3))`:
       - `(%for (kw val) in (%items  %dict) (%log %kw = %val))`
       - `(%for  kw      in (%keys   %dict) (%log %kw = (%get %kw %dict)))`
       - `(%for     val  in (%values %dict) (%log ___ = %val))`
 - [ ] Extend `%get` to work with slicing `(%get (1 3) (a b c d e))` becomes `b c d`; negative indices `(%get -1 (a b c))` becomes `c`.
 - [ ] Shell-style `${var:...}` string manipulation.
 - [ ] `%while`, `%take`, `%drop`, `%split` on symbols in lists, `%intercalate`.
 - [ ] `(%basename :suffix "txt" /path/file.txt)` (-> `file`), `(%dirname /path/file.txt)` (-> `/path`) and `(%extension /path/file.txt)` (-> `txt`), macros for paths.
 - [ ] Math operators: `+`, `-`, `*`, `/`, `mod`, `pow`, `exp`, `sqrt`, `log`, `ln`, `hypot`.
 - [ ] User `(%error msg)` macro for aborting compilation.
 - [x] List reverse macro `(%reverse (...))`.
 - [x] Literal/atomic conversion macros: `(%symbol lit)`, `(%number lit)`, `(%string lit)`, `(%raw lit)`.
 - [x] Sorting macro `(%sort (...))` which sorts alphanumerically on literals.
       Allow providing a `:key` to sort "by field": e.g. sort by title name `(%sort :key (%lambda ((:title _ &&_)) %title) %posts)`
 - [x] Extend the strftime-style `(%date)` to be able to read UNIX numeric timestamps and display relative to timezones.
       Add complementary strptime-style utility `(%timestamp)` to convert date-strings to timestamps (relative to a timezone).
 - [x] Pattern-matching `(%match expr (pat1 ...) (pat2 ...))` macro.
       Pattern matching is already implemented for `%define` internally.
 - [x] The trailing keyword-matching operator. `&&rest` matches excess keyword.
       Extracting a value from a map `(:a 1 :b 2 :c 3)` is done with:
       `(%match %h ((:b default &&_) %b))`.
 - [x] `%get` macro: `(%get b (:a 1 :b 2))` becomes `2`; `(%get 0 (a b c))` becomes `a`.
 - [x] `(%yaml "...")`, `(%toml "...")` and `(%json "...")` converts
       whichever config-lang definition into a seam `%define`-definition.
 - [x] `(%do ...)` which just expands to the `...`; the identity function.
 - [ ] Catch expansion errors: `(%try :catch index-error (%do code-to-try) :error the-error (%do caught-error %the-error))`.
 - [x] Implement `(%strip ...)` which evaluates to the `...` without any of the leading whitespace.
 - [x] Implement *splat* operation: `(%splat (a b c))` becomes `a b c`.
 - [x] `(%define x %body)` evaluates `%body` eagerly (at definition),
       while `(%define (y) %body)` only evaluates `%body` per call-site `(%y)`.
 - [x] Namespace macro `(%namespace ns (%include "file.sex"))` will prefix all definitions in its body with `ns/`, e.g. `%ns/defn`.
       Allows for a customizable separator, e.g. `(%namespace ns :separator "-" ...)` will allow for writing `%ns-defn`.
       Otherwise, the macro leaves the content produced by the body completely unchanged.
 - [x] Command line `-I` include directory.
 - [x] First argument in a macro invocation should have its whitespace stripped.
 - [x] `(%os/env ENV_VAR)` environment variable macro.
 - [ ] Lazy evaluation for *user* macros (like in `ifdef`) with use of new `(%eval ...)` macro.
 - [x] `(%apply name x y z)` macro which is equivalent to `(%name x y z)`.
 - [x] `(%lambda (x y) ...)` macro which just evaluates to an secret symbol, e.g. `__lambda0`.
       used by applying `%apply`, e.g. `(%apply (%lambda (a b) b a) x y)` becomes `y x`
 - [x] `(%string ...)`, `(%join ...)`, `(%map ...)`, `(%filter ...)` macros.
 - [x] `(%concat ...)` which is just `(%join "" ...)`.
 - [x] Add options to `%glob` for sorting by type, date(s), name, etc.
 - [x] `(%format "{}")` macro with Rust's `format` syntax. e.g. `(%format "Hello {}, age {age:0>2}" "Sam" :age 9)`
 - [x] Add `(%raw ...)` macro which takes a string and leaves it unchanged in the final output.
 - [ ] `(%formatter/text ...)` can take any seam (sexp) source code, for which it just embeds the expanded code (plain-text formatter).
 - [ ] `(%formatter/html ...)` etc. which call the respective available formatters.
 - [ ] Implement lexical scope by letting macros store a copy of the scope they were defined in (or a reference?).
 - [x] `(%embed "/path")` macro, like `%include`, but just returns the file contents as a string.
 - [x] Variadic arguments via `&rest` syntax.
 - [ ] Type-checking facilities for user macros.
 - [x] `%list` macro which expands from `(%list %a %b %c)` to `( %a %b %c )` but *without* calling `%a` as a macro with `%b` and `%c` as argument.
 - [x] `%for`-loop macro, iterating over `%list`s.
 - [x] `%glob` which returns a list of files/directories matching a glob.
 - [x] `%markdown` renders Markdown given to it as `%raw` html-string.
 - [x] Add keyword macro arguments.
 - [ ] Caching or checking time-stamps as to not regenerate unmodified source files.
 - [ ] HTML object `style="..."` object should handle s-expressions well, (e.g. `(p :style (:color red :border none) Hello World)`)
 - [ ] Add more supported formats (`JSON`, `JS`, `TOML`, &c.).
 - [ ] Allow for arbitrary embedding of code with their REPLs, that can be run by
   a LISP interpreter (or any other language), for example.  (e.g. `(%chez (+ 1 2))` executes
   `(+ 1 2)` with Chez-Scheme LISP, and places the result in the source (i.e. `3`).
