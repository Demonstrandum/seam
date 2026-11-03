# Usage

## Syntax

### Overview

The syntax consists of *symbolic expressions*, which may be any of:
- Symbols (e.g. `p`, `h1` or `hello`).
- Numbers (e.g. `26`, `2em` or `-4px`).
- Strings (e.g. `"hello world"` or `"""Probably a long string"""`).
- Attributes (e.g `:key value`, `:count 6` or `:href "https://crates.io/"`).
- Lists (e.g. `(h1 Big Title!)` or `(p Hello (span :class highlight World))`).

The most important part of this syntax is *lists*, every level of nesting or
every tag is started with a `(` and ended with a `)`

### Example

For example,
```lisp
(h1 :id heading Pound Cake)
(ul (li 1 pound of sugar)
	(li 1 pound of butter)
	(li 1 pound of (i self-raising) flor)
	(li 3 eggs, beaten)
	(li 1 teaspoon (a :href "https://wikipedia.org/wiki/Vanilla_extract" vanilla))
	(li 1 teaspoon baking powder))
```
would translate to HTML as
```html
<h1 id="heading">Pound Cake</h1>
<ul>
	<li>1 pound of sugar</li>
	<li>1 pound of butter</li>
	<li>1 pound of <i>self-raising</i> flour</li>
	<li>3 eggs, beaten</li>
	<li>1 teaspoon <a href="https://wikipedia.org/wiki/Vanilla_extractr">vanilla</a></li>
	<li>1 teaspoin baking powder</li>
</ul>
```

### HTML documents

With `--html`, seam completes the document for you, unless `--nodocument`
is given. Missing `(!DOCTYPE html)`, `(html ...)`, `(head ...)` and `(body ...)`
elements are added, the same way browsers treat HTML with those tags omitted:
loose metadata (`title`, `meta`, `link`, `style`, `script`, `base`, `noscript`,
`template`) goes into the `<head>` until the first piece of content, and from
then on everything goes into the `<body>`.
```lisp
(title Pound Cake)
(h1 Pound Cake)
```
becomes
```html
<!DOCTYPE html>
<html>
<head>
<title>Pound Cake</title>
</head>
<body>
<h1>Pound Cake</h1>
</body>
</html>
```
Any of these elements written explicitly are kept as they are (along with
their attributes, e.g. `(html :lang en ...)`). Only the top-level, and the
inside of `(html ...)`, are looked at.

Inside `(pre ...)`, macros and variables are expanded as they are anywhere
else, so `(pre (%embed "example.c"))` shows that file. When nothing inside
was expanded, the contents are copied exactly as written, including their
spacing, parentheses and `;` comments. The text of `pre`, `title` and
`textarea` is always HTML-escaped.

### Literate mode

In *literate* mode, source is plain text, kept exactly as written, and only
macro calls `(%...)` are parsed and expanded. Inside a macro call, the usual
syntax applies. Write `\(%` for a literal `(%`.
```sh
seam --html --nodocument --literate <<< '(%define name Sam)<p>Hi (%name), see (%do (a :href "/" home)).</p>'
#stdout:
#   <p>Hi Sam, see <a href="/">home</a>.</p>
```
This is handy for templating any kind of text, such as hand-written HTML or Markdown.
Literate mode is enabled with:
- `--literate` on the command line;
- `:literate true` for `(%include ...)`, and for `(%embed ...)`, which then
  expands the file's macros rather than giving its contents as a string;
- `(%markdown ...)`, where it is on by default (disable it with `:literate false`).
  Elements produced by macros within Markdown are written as HTML.

## Macros

In addition to the basic syntax, *symbols* prepended with a ‘`%`’ character,
will be treated as macros.

### Built-in Macros
- `%define` allows for user defined macros, e.g. `(%define name "Samuel")`,
  ‘function’-like macros may also be defined to allow arguments, say
  `(%define (greet name) (p Hello there, %name))`.
- `%ifdef` checks if a symbol is defined, e.g. `(ifdef username (span Hello %username))`,
  or with an else-clause: `(ifdef title (title My Blog - %title) (title My Blog))`.
- `%include` will include an entire file's contents into another, e.g.
  `(%include "components/footer.sex")`.
- `%date` standard `strftime` function, works of current system time, e.g.
  `(span :id timestamp Uploaded on (%date "%Y-%m-%d"))`.
- `%log` will simply log any information to STDERR, e.g. `(%log Hello, World!)`.
- `%with` overrides top-level definitions for everything within it, e.g.
  `(%with (:title "Pound Cake") (%layout))` (see [Scoping](#scoping)).

### Scoping

Macros are *lexically* scoped: a macro's body sees the definitions from where
the macro was *defined*, plus its own parameters, never those of whoever calls it.
```lisp
(%define x global)
(%define (show) %x)
(%define (f x) (%show))
(%f local)  ; → global
```
This means `%lambda` makes closures, which keep their definitions after
the macro that made them has returned,
```lisp
(%define (adder n) (%lambda (x) %n plus %x))
(%apply (%adder 1) 2)  ; → 1 plus 2
```
and macros defined inside a `%namespace` keep using the namespace's own helpers.

Definitions made inside a macro's body, `%for` or `%match` stay local to it.
Plain lists don't make a new scope, and `%include` behaves as if the file's
contents were written in place, so definitions it makes are visible after it.

To pass values implicitly through macro calls, such as from a page into a
shared layout, use `%with`. Its bindings override *top-level* definitions
for everything expanded within it, including other macros it calls, but they
never override a macro's parameters or local definitions.
```lisp
(%define title "My Website")  ; Default.
(%define (layout) (title %title))
(%layout)                               ; → (title "My Website")
(%with (:title "Pound Cake") (%layout)) ; → (title "Pound Cake")
```
The bindings may come from any expression giving keyword-value pairs,
e.g. `(%define (page &&meta) (%with %meta (%layout)))`.

## Library

When using seam as a Rust library, expansion needs a `Context`, which owns
every source file and scope, so the expanded tree may borrow from them:
```rust
let context = seam::Context::new();
let expander = seam::tree_builder_file(&context, path)?;
let tree = expander.expand()?;
```

### Example

*File `head.sex`:*
```lisp
(meta :name viewport :content "width=device-width, initial-scale=1.0")
(%ifdef title
	(title %title" -- My Website")
	(title "My Website"))
(style (%include "styles/main.sex"))
```

*File `styles/main.sex`:*
```lisp
(body :font-size 16px
      :margin (0 auto)
      :background #fff)
(.important
  :color red)
```

*File `index.sex`:*
```lisp
(!doctype html)
(html :lang en
  (head (%define title "Index page")
        (%include "head.sex"))
  (body
    (div :id container
      (%include "components/navbar.sex")
      (h1 Hello, World!)
      (p :class important Enjoy your stay!))))
```

*File `components/navbar.sex`:*
```lisp
(nav
  (ul (li (a :href "/" Home))
      (li (a :href "/about" About Me))
      (li (a :href "/donate" Donate!))))
```

This way you can easily construct websites with reusable components,
cut down on copy-pasting, and generate it statically. Ideal for a blog,
especially using the `(%markdown ...)` macro.
