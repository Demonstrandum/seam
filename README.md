# SEAM

> **S**ymbolic **E**xpressions **A**s **M**arkup.

## Why

Because all markup is terrible, especially XML/SGML and derivatives.

But mainly, for easier static markup code generation, such as with
macros, code includes and such.


## Try it out

Mainly this should be used as a library, such as from within a server,
generating HTML (or any other supported markup) before it is served to the
client.

### Current Formats
 - XML
 - HTML
 - CSS

## TODO
 - Caching or checking time-stamps as to not regenerate unmodified source files.
 - HTML object `style="..."` object should handle s-expressions well, (e.g. `(p :style (:color red :border none) Hello World)`)
 - HTML `<style>` tag should allow for *normal* CSS syntax if just given a string.
 - Allow for, and handle special `@` syntax in CSS, such as `@import` and `@media`.
 - Add more supported formats (`JSON`, `JS`, `TOML`, &c.).
 - Add more helpful/generic macros (e.g. `(%include ...)`, which already exists).
 - Add user defined macros system (e.g. `(%define (red-para txt) (p :style "color: red" %txt))`)
 - Then add variadic macros.
 - Allow for arbitrary embedding of code, that can be run by
   a LISP interpreter (or any other langauge), for example.  (e.g. `(%chez (+ 1 2))` executes
   `(+ 1 2)` with Chez-Scheme LISP, and places the result in the source
   (i.e. `3`).

### Using The Binary

(Providing you have cloned this repo, and `cd`'d into it)

```console
cargo run test.sex --html > test.html
```

`test.sex` contains your symbolic-expressions, which is used to generate
HTML, saved in `test.html`.
