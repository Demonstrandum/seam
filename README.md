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

### Using The Binary

(Providing you have cloned this repo, and `cd`'d into it)

```console
cargo run test.sex --html > test.html
```

`test.sex` contains your symbolic-expressions, which is used to generate
HTML, saved in `test.html`.
