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
