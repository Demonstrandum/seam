# JavaScript in seam

How all of JavaScript (ES2025, and the older constructs) is written as
s-expressions, for `--js`, `%formatter/js` and HTML `script` elements.

## Principles

1. **A list is `(head arguments...)`.** If the head is one of the forms
   below, it is that form; otherwise the list is a call, `(f a b)` → `f(a, b)`.
2. **Forms are JavaScript keywords, operators, or a few plain words**
   (`array`, `object`, `key`, `regex`, `field`, ...).
   To call a function that has the same name as a form, escape it:
   `(\array 5)` → `array(5)`. Words that JavaScript only treats as keywords in
   some places (`of`, `as`, `from`, `default`, `get`, `set`, `static`,
   `async`, `constructor`) are only special in those same places.
3. **No precedence.** A nested operation is always put in parentheses, so
   `(* (+ a b) c)` → `(a + b) * c`, and what you write is what runs.
4. **Atoms are written as they are,** except strings, which are written as
   JavaScript strings. So names, `this`, `true`, `null`, numbers, `10n`,
   `#private`, `i++`, `a.b.c` and simple regexes (`/a+/g`) need no form.
5. **Seam's own syntax still applies:** `;` starts a comment, `%` calls a
   macro, `"` starts a string and `:` starts a keyword. Escape a character
   with `\` to use it in a symbol: `(\% a b)` → `a % b`. Macros run before
   the JavaScript is written, so `(const n %count)` puts a seam value into it.
6. **`(%raw "...")` is written exactly as given,** for anything not covered.

## Literals

| Seam | JavaScript |
|---|---|
| `x`, `this`, `null`, `undefined`, `NaN` | the same |
| `42`, `0x1F`, `1e3`, `10n`, `1_000` | the same |
| `"a \"b\"\n"` | `"a \"b\"\n"` |
| ``(` "Hi, " name "!")`` | `` `Hi, ${name}!` `` (strings are text, anything else is `${...}`) |
| ``(` :tag html "<p>" x "</p>")`` | ``html`<p>${x}</p>` `` |
| `/a+b/gi` | `/a+b/gi` (as a symbol) |
| `(regex "a b;c" gi)`, `(regex "a b")` | `/a b;c/gi`, `/a b/` (any pattern, flags optional) |

## Arrays and objects

| Seam | JavaScript |
|---|---|
| `(array 1 2 (... rest))`, `(array)` | `[1, 2, ...rest]`, `[]` |
| `(array 1 () 3)` | `[1, , 3]` (`()` is a hole) |
| `(:a 1 :b-c 2)` | `{a: 1, "b-c": 2}` (a list of attributes, as in JSON) |
| `(object :a 1 b (... other))` | `{a: 1, b, ...other}` (a bare name is shorthand) |
| `(object (key k 1))` | `{[k]: 1}` (a computed key) |
| `(object (greet (name) ...) (get size () ...) (set size (n) ...))` | `{greet(name) {...}, get size() {...}, set size(n) {...}}` |
| `(object (async (load () ...)) (* items () ...))` | `{async load() {...}, *items() {...}}` |
| `(object (([] Symbol.iterator) () ...))` | `{[Symbol.iterator]() {...}}` |
| `(object)` | `{}` |

## Property access and calls

| Seam | JavaScript |
|---|---|
| `(. a b c)` | `a.b.c` |
| `([] a i)`, `([] a i j)` | `a[i]`, `a[i][j]` |
| `(. a b ([] i) "x-y" 0)` | `a.b[i]["x-y"][0]` (`([] i)` is a computed key, as are strings and numbers) |
| `(?. a b)`, `(?. a ([] i))` | `a?.b`, `a?.[i]` (every step is optional) |
| `(. (?. a b) c)` | `a?.b.c` |
| `((. a b) 1 2)`, `(a.b 1 2)` | `a.b(1, 2)` |
| `(f?. x)`, `(a.b?. x)` | `f?.(x)`, `a.b?.(x)` |
| `(new Map)`, `(new Map (... pairs))` | `new Map()`, `new Map(...pairs)` |
| `(super x)`, `(. super method)` | `super(x)`, `super.method` |
| `(import "./a.js")` as an expression | `import("./a.js")` |
| `new.target`, `import.meta` | the same |

## Operators

| Seam | JavaScript |
|---|---|
| `(+ a b c)`, `(- a b)`, `(* a b)`, `(/ a b)`, `(\% a b)`, `(** a b)` | `a + b + c`, ... |
| `(- a)`, `(+ a)`, `(! a)`, `(~ a)` | `-a`, `+a`, `!a`, `~a` |
| `(typeof a)`, `(void a)`, `(delete (. a b))`, `(await p)` | `typeof a`, ... |
| `(== a b)`, `(=== a b)`, `(!= a b)`, `(!== a b)`, `(< a b)`, ... | exactly two operands |
| `(&& a b c)`, `(\|\| a b)`, `(?? a b)` | `a && b && c`, ... |
| `(& a b)`, `(\| a b)`, `(^ a b)`, `(<< a b)`, `(>> a b)`, `(>>> a b)` | bitwise |
| `(in k o)`, `(instanceof x C)`, `(in #x o)` | `k in o`, `x instanceof C`, `#x in o` |
| `(? c a b)` | `c ? a : b` |
| `(, a b c)` | `(a, b, c)` |
| `(++ x)`, `(-- x)`, `(++post x)`, `(--post x)` | `++x`, `--x`, `x++`, `x--` (or just the atoms `++i`, `i++`) |
| `(= x 1)`, `(+= x 1)`, `(\%= x 2)`, `(??= x 0)`, `(&&= x y)`, ... | assignment |
| `(= (array a b) (array b a))` | `[a, b] = [b, a]` (patterns, below) |
| `(yield x)`, `(yield* xs)`, `(yield)` | `yield x`, ... |

## Patterns (destructuring)

A pattern is wherever a name is bound: declarations, parameters, `for` and
`catch` bindings, and the left of `=`.

| Seam | JavaScript |
|---|---|
| `(array a b (... rest))`, `(array a () c)` | `[a, b, ...rest]`, `[a, , c]` |
| `(object a :b c (= d 1) (... rest))` | `{a, b: c, d = 1, ...rest}` |
| `(object :b (object c))`, `(object (key k v))` | `{b: {c}}`, `{[k]: v}` |
| `(= x 1)` in a pattern or parameters | `x = 1` (a default) |

## Declarations

| Seam | JavaScript |
|---|---|
| `(const x 1)`, `(let x)`, `(var x 1)` | `const x = 1;`, ... |
| `(const (object a b) obj)` | `const {a, b} = obj;` |
| `(let (a 1) (b 2) (c))` | `let a = 1, b = 2, c;` (when the first argument is a list, but not a pattern) |
| `(using r (open))`, `(await-using r (open))` | `using r = open();`, `await using ...` |

## Functions

A function returns its last expression, unless that is a statement or the
function is a generator, constructor or setter.

| Seam | JavaScript |
|---|---|
| `(function add (a b) (+ a b))` | `function add(a, b) { return a + b; }` |
| `(function (a) ...)` | an anonymous function expression |
| `(function* gen () (yield 1))` | `function* gen() {...}` |
| `(=> (x (= y 1) (... zs)) body...)` | `(x, y = 1, ...zs) => ...` |
| `(=> (x) (:a x))` | `(x) => ({a: x})` |
| `(async (function f () ...))`, `(async (=> () ...))`, `(async (function* ...))` | `async function f() {...}`, ... |
| `(return)` as the last statement | no value is returned |

## Classes

| Seam | JavaScript |
|---|---|
| `(class Point :extends Base members...)` | `class Point extends Base {...}` |
| `(class members...)`, `(class :extends Base ...)` | a class expression |
| `(constructor (x y) (super) (= (. this x) x))` | `constructor(x, y) {...}` |
| `:x 0`, `:#count 0`, `(field x)` | fields `x = 0;`, `#count = 0;`, `x;` |
| `(norm () ...)`, `(#helper () ...)`, `(([] Symbol.iterator) () ...)` | methods |
| `(get size () ...)`, `(set size (n) ...)` | accessors |
| `(static :count 0)`, `(static (create () ...))` | static members |
| `(static (do ...))` | a static block |
| `(async (load () ...))`, `(* items () ...)` | async and generator methods |
| `(\get () ...)` | a method named `get` |

## Statements

| Seam | JavaScript |
|---|---|
| `(do a b)` | `{ a; b; }` (a block) |
| `(if c a)`, `(if c a b)`, `(if c a (if d b e))` | `if`, `else`, `else if` (use `(do ...)` for several statements) |
| `(for (let i 0) (< i n) (++ i) body...)` | `for (let i = 0; i < n; ++i) {...}` (`()` for an empty part) |
| `(for x of xs body...)`, `(for k in o body...)` | `for (const x of xs) {...}` |
| `(for (let x) of xs ...)`, `(for (array k v) of m ...)` | `let`, or a pattern |
| `(for-await x of xs ...)` | `for await (const x of xs) {...}` |
| `(while c body...)`, `(do-while c body...)` | `while`, `do {...} while (c);` |
| `(switch x (case 1 a) (case 2) (case 3 b (break)) (default c))` | `switch` (a `case` with no body falls through) |
| `(try body... (catch e ...) (finally ...))` | `try` (`(catch () ...)` has no binding) |
| `(throw e)`, `(return x)`, `(return)` | the same |
| `(break)`, `(continue)`, `(break outer)` | the same |
| `(outer: (for ...))` | `outer: for ...` (a head ending in `:` is a label) |
| `(debugger)`, `(with o body...)` | the same |
| `"use strict"` as a statement | `"use strict";` |
| `(// "text")`, `(/* "text")` | `// text`, `/* text */` (comments in the output) |

## Modules

Imports and exports keep JavaScript's word order. A list of names is `{...}`.

| Seam | JavaScript |
|---|---|
| `(import "./a.js")` as a statement | `import "./a.js";` |
| `(import D from "./a.js")` | `import D from "./a.js";` |
| `(import (as * ns) from "./a.js")` | `import * as ns from "./a.js";` |
| `(import D (a (as b c)) from "./a.js")` | `import D, {a, b as c} from "./a.js";` |
| `(import data from "./d.json" :with (:type "json"))` | `import data from "./d.json" with {type: "json"};` |
| `(export (const x 1))`, `(export (function f () ...))` | `export const x = 1;`, ... |
| `(export default expr)` | `export default expr;` |
| `(export (a (as b c)))` | `export {a, b as c};` |
| `(export (a) from "./a.js")`, `(export * from "./a.js")`, `(export (as * ns) from "./a.js")` | re-exports |

## Notes

- Names are written as they are, so a kebab-case `my-name` is written as
  `my-name`, which JavaScript reads as `my - name`.
- `(a.b 1)` works because symbols are written as they are; `(. a b)` is
  the same, and works on any expression.
