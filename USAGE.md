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
  Frontmatter and content are expanded separately, so `:only frontmatter`
  or `:only content` expands just that part, and the content can use the
  frontmatter's definitions. Macro calls inside code (blocks and spans) are
  shown as written, not expanded.

### Running build scripts

`seam run file.sex` expands a file only for what its macros *do*, such as
writing files with `%write` or running programs with `%exec`, and discards
the document it would otherwise generate. Like `make`, it reports each action
on STDOUT as it happens, and `%log` prints there too:
```sh
seam run build.sex
#stdout:
#   write public/index.html
#   write public/posts/hello-world.html
#    exec git rev-parse --short HEAD
#     log Built 3 posts.
```
No target format is given, and the other options (`-I`, `--literate`) work as usual.

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
  `(%include "components/footer.sex")`. Paths are looked up relative to the
  including file first, then in each include directory (`-I`, and the
  working directory). `%embed` finds files the same way.
- `%date` standard `strftime` function, works of current system time, e.g.
  `(span :id timestamp Uploaded on (%date "%Y-%m-%d"))`.
- `%log` will simply log any information to STDERR (STDOUT under `seam run`),
  e.g. `(%log Hello, World!)`.
- `%with` overrides top-level definitions for everything within it, e.g.
  `(%with (:title "Pound Cake") (%layout))` (see [Scoping](#scoping)).
- `%let` binds patterns for its body, each seeing the ones before it, e.g.
  `(%let ((n 2) ((a b) (x y))) %n %a %b)`.

#### Conditions and arithmetic
- `(%if condition then else)` expands only the chosen branch. Nothing, `()`,
  `false` (or `"false"`, as YAML and TOML booleans arrive) and `""` are false;
  anything else is true.
- `%not`, `%and` and `%or`, where `%and` and `%or` stop expanding their
  arguments as soon as the answer is known.
- Comparisons `%=`, `%!=`, `%<`, `%>`, `%<=` and `%>=` (numbers by value,
  anything else by its text), e.g. `(%< 1 %n 10)`.
- Arithmetic `%+`, `%-`, `%*`, `%/`, `%mod`, `%pow`, `%min`, `%max`, and
  `%exp`, `%sqrt`, `%ln`, `%log2`, `%log10`, `%abs`, `%floor`, `%ceil`,
  `%round` and `%hypot`. Whole numbers stay whole where possible:
  `(%/ 6 3)` is `2`, `(%/ 7 2)` is `3.5`. (`%log` already logs to STDERR,
  hence `%ln`, `%log2` and `%log10`.)
- `(%range first last step)`, the numbers from first to last inclusive.

#### Lists
- `(%get 1 list)`, `(%get -1 list)` (from the end), `(%get key dict)`,
  `(%get a/b nested)`, and `(%get (1 3) list)` for a slice (inclusive).
- `(%take n list)`, `(%drop n list)`, and `(%while predicate list)`, the
  items before the first one the predicate macro is false for.
- `(%split , "a,b")` gives `("a" "b")`; `(%split | (a b | c))` gives `((a b) (c))`.
- `(%intercalate ", " %tags)` puts the separator between the items (unwrapped).
- `(%length list)` counts items, or the characters of a string.
- `(%unique list)` drops repeated items; `(%contains item list)` tests membership.
- `(%items dict)`, `(%keys dict)` and `(%values dict)` for keyword lists:
  `(%for (key value) in (%items (:a 1 :b 2)) ...)`.
- `%for` iterates over the items of the list its expression gives
  (or over all the nodes it gives), e.g. `(%for post in %posts ...)`.

#### Paths, files and programs
- `(%basename :suffix md posts/hi.md)` → `hi`, `(%dirname posts/hi.md)` →
  `posts`, `(%extension posts/hi.md)` → `md` (also `%path/basename`,
  `%path/dirname` and `%path/extension`).
- `(%path/cwd)` is the (absolute) directory seam is run from, and
  `(%path/this)` is the absolute path of the file the call is written in, and
  `(%path/here)` is its directory (the current directory, for
  source read from STDIN). Relative paths given to `%glob`, `%write`, `%exec`
  and the like are from the current directory, so
  `(%path/join (%path/here) posts)` refers to `posts` next to the
  file wherever seam is run from.
- `(%path/join a b/c d.txt)` → `a/b/c/d.txt`, and `(%path/split /a/b.md)` →
  `("/" a b.md)`.
- `(%path/stem a/b.tar.gz)` → `b.tar`, `(%path/with-extension a/b.md html)` →
  `a/b.html` (an empty extension removes it).
- `(%path/normalise a/./b/../c)` → `a/c`, without looking at the file system,
  while `(%path/canonical path)` resolves links too, and the file must exist.
- `(%path/absolute path :from dir)` resolves a path from a directory (by default,
  the current one), and `(%path/relative path :from dir)` gives the way to a path
  from a directory: `(%path/relative /a/b/c :from /a/d)` → `../b/c`.
- `(%path/exists path)`, `(%path/is-file path)` and `(%path/is-directory path)`
  are `true` or `false`.
- `(%write path content...)` writes the content's text to a file (making
  directories as needed), expanding to nothing. With the formatter macros
  below, one source file can generate a whole site, run with `seam run`.
- `(%exec program arguments... :stdin text)` runs a program and gives its
  output, e.g. `(%exec git rev-parse --short HEAD)`.

#### Errors
- `(%error message...)` stops with an error.
- `(%try expression :error name fallback...)` gives the expression, or if it
  fails, the fallback, with `%name` bound to the error message.

#### Code as data
- `(%quote ...)` gives its arguments unexpanded; `(%eval ...)` expands its
  arguments, then expands the result: `(%eval (%quote (%+ 1 2)))` → `3`.

#### Formatters
- `(%formatter/html ...)`, `(%formatter/xml ...)`, `(%formatter/css ...)`,
  `(%formatter/text ...)` and `(%formatter/sexp ...)` generate their arguments
  with that formatter, as text. Markup is kept as it is (raw), while text and
  s-expressions are escaped in the output. `:document true` generates a whole
  document, e.g. `(%write "out/index.html" (%formatter/html :document true ...))`.

#### Shell-style variables
`%{name...}` manipulates a variable's text, as `${name...}` does in a shell:

| Form | Gives |
|---|---|
| `%{name}` | the value |
| `%{#name}` | its length |
| `%{name:-default}` / `%{name:+other}` | `default` if unset or empty / `other` if set |
| `%{name:2}`, `%{name:2:3}`, `%{name:0-3}` | from offset 2; 3 characters from 2; the last 3 |
| `%{name#glob}`, `%{name##glob}` | without the shortest / longest matching prefix |
| `%{name%glob}`, `%{name%%glob}` | without the shortest / longest matching suffix |
| `%{name/glob/to}`, `%{name//glob/to}` | first / every match replaced |
| `%{name/#glob/to}`, `%{name/%glob/to}` | a matching prefix / suffix replaced |
| `%{name^}`, `%{name^^}`, `%{name,}`, `%{name,,}` | first letter / all upper case; lower case |

These can't contain spaces, since a space ends the symbol.

### Defining macros

`(%define (name parameters...) body...)` makes a macro, called as
`(%name arguments...)`. Its parameters are patterns:
- `x` binds a positional argument, and `(a b)` destructures a list;
- `&rest` binds the remaining positional arguments;
- `:key default` binds the keyword argument `:key`, or else the default;
- `&&rest` binds the remaining keyword arguments.

Parameters may be **typed** with the same types as the built-in macros use
(`literal`, `string`, `symbol`, `number`, `symbolic`, `list`, `any`), checked
on every call: `n:number`, `&items:string`, `:sep:string ", "`.

A parameter prefixed with `~` is **lazy**: its argument is not expanded
before the call. Instead, each use of `%param` expands the argument as it was
written, in the caller's scope. This lets macros decide what to evaluate:
```lisp
(%define (unless condition ~body) (%if %condition () %body))
(%unless %draft (%include "comments.sex"))
(%define (twice ~&body) %body %body)  ; Lazy rest.
```
Since `%if` is lazy too, macros can be recursive:
```lisp
(%define (fact n:number) (%if (%<= %n 1) 1 (%* %n (%fact (%- %n 1)))))
```

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

See [`samples/blog`](samples/blog) for a whole blog: Markdown posts with
frontmatter, a shared layout, a tags page and an RSS feed, all generated by
`seam run build.sex` with `%write` and the formatter macros.
