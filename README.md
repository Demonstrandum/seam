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
 - SEXP (`--sexp`; S-expression, basically a macro expansion utility)

### Installation

You may clone the repo, then build and install
```sh
git clone git://git.knutsen.co/seam
cd seam
cargo build --release
cargo install --path .
```

Or install it from crates.io
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

## TODO
 - Escape evaluating macros with `\%`.
 - `(%format "{}")` macro with Rust's `format` syntax.
 - Implement lexical scope by letting macros store a copy of the scope they were defined in (or a reference?).
 - `(%embed "/path")` macro, like `%include`, but just returns the file contents as a string.
 - Variadic arguments via `&rest` syntax.
 - Delayed evaluation of macros by `%(...)` synatx.
   For example `%(f x y)` is the same as `(%f x y)`, so you can have `(%define uneval f x)` and then write `%(%uneval y)`.
 - `%list` macro which expands from `(p (%list a b c))` to `(p a b c)`.
    Defined as such:
    ```lisp
    (%define (list &rest) rest)
    ```
 - `%for`-loop macro, iterating over `%list`s.
 - `%glob` which returns a list of files/directories matching a glob.
 - `%markdown` renders Markdown given to it as html.
 - `%html`, `%xml`, `%css`, etc. macros which goes into the specific rendering mode.
 - Add variadic and keyword macro arguments.
 - Caching or checking time-stamps as to not regenerate unmodified source files.
 - HTML object `style="..."` object should handle s-expressions well, (e.g. `(p :style (:color red :border none) Hello World)`)
 - Add more supported formats (`JSON`, `JS`, `TOML`, &c.).
 - Maybe: a whole JavaScript front-end, e.g.
   ```lisp
   (let x 2)
   (let (y 1) (z 1))
   (const f (=> (a b) (+ a b))
   ((. console log) (== (f y z) x))
   ```
 - Add more helpful/generic macros (e.g. `(%include ...)`, which already exists).
 - Allow for arbitrary embedding of code, that can be run by
   a LISP interpreter (or any other langauge), for example.  (e.g. `(%chez (+ 1 2))` executes
   `(+ 1 2)` with Chez-Scheme LISP, and places the result in the source
   (i.e. `3`).
