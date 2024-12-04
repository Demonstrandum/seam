# SEAM

> **S**ymbolic **E**xpressions **A**s **M**arkup.

## Why

Because all markup is terrible, especially XML/SGML and derivatives.

But mainly, for easier static markup code generation, such as with
macros, code includes and such.

## Try it out

This may be used as a library, such as from within a server,
generating HTML (or any other supported markup) before it is served to the
client.  Personally, I am currently just using the `seam` binary to statically
generate some personal and project websites.

Read the [USAGE.md](USAGE.md) file for code examples and documentation.

### Current Formats

 - XML (`--xml`; including: SVG, MathML)
 - HTML (`--html`; SGML)
 - CSS (`--css`)
 - SExp (`--sexp`; S-expression, basically a macro expansion utility)
 - Plain Text (`--text`; renders escaped strings to text)

### Installation

You may clone the repo, then build and install
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

You may use it by doing
```sh
seam test.sex --html > test.html
```

`test.sex` contains your symbolic-expressions, which is used to generate
HTML, saved in `test.html`.

Likewise, you may read from `STDIN`
```sh
seam --html < example.sex > example.html
# Which is the same as
cat example.sex | seam --html > example.html
```
You may also very well use here-strings and here-docs, if your shell
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
 - [ ] User `(%error msg)` macro for aborting compilation.
 - [ ] Pattern-matching `(%match expr (pat1 ...) (pat2 ...) default)` macro.
   Pattern matching is already implemented for `%define` internally.
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
 - [x] `(%format "{}")` macro with Rust's `format` syntax. e.g. `(%format "Hello {}, age {age:0>2}" "Sam" :age 9)`
 - [x] Add `(%raw ...)` macro which takes a string and leaves it unchanged in the final output.
 - [ ] `(%formatter/text)` can take any other source code, for which it just embeds the expanded code (plain-text formatter).
 - [ ] `(%formatter/html ...)` etc. which call the respective available formatters.
 - [ ] Implement lexical scope by letting macros store a copy of the scope they were defined in (or a reference?).
 - [x] `(%embed "/path")` macro, like `%include`, but just returns the file contents as a string.
 - [x] Variadic arguments via `&rest` syntax.
 - [ ] Type-checking facilities for user macros.
 - [x] `%list` macro which expands from `(%list %a %b %c)` to `( %a %b %c )` but *without* calling `%a` as a macro with `%b` and `%c` as argument.
 - [ ] `%for`-loop macro, iterating over `%list`s.
 - [ ] `%glob` which returns a list of files/directories matching a glob.
 - [ ] `%markdown` renders Markdown given to it as `%raw` html-string.
 - [ ] Add keyword macro arguments.
 - [ ] Caching or checking time-stamps as to not regenerate unmodified source files.
 - [ ] HTML object `style="..."` object should handle s-expressions well, (e.g. `(p :style (:color red :border none) Hello World)`)
 - [ ] Add more supported formats (`JSON`, `JS`, `TOML`, &c.).
 - [ ] Maybe: a whole JavaScript front-end, e.g.
   ```lisp
   (let x 2)
   (let (y 1) (z 1))
   (const f (=> (a b) (+ a b))
   ((. console log) (== (f y z) x))
   ```
 - [ ] Allow for arbitrary embedding of code, that can be run by
   a LISP interpreter (or any other langauge), for example.  (e.g. `(%chez (+ 1 2))` executes
   `(+ 1 2)` with Chez-Scheme LISP, and places the result in the source
   (i.e. `3`).
