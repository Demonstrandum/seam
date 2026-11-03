---
title: Macros All the Way Down
date: 2024-05-02
tags: [seam, macros]
description: The index, tags page and feed are all built from macros.
---

The list of posts on the index isn't written by hand. `site.sex` globs the
`posts/` directory, reads each post's frontmatter, drops the drafts and
sorts the rest by date:

```lisp
(%define posts
  (%sort :order descending :key (%lambda ((:date _ &&_)) %date)
    (%list (%for file in (%glob "posts/*.md")
      (%let ((post (%read-post %file)))
        (%if (%not (%get draft %post)) %post))))))
```

The reading time beside each post is arithmetic on its word count, and the
tags page is just `%unique` over every post's tags.

Markdown is *literate*: text is left alone, but macro calls are expanded,
so this sentence can say that two squared is (%pow 2 2).
