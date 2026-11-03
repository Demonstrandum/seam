---
title: One File, Many Pages
date: 2024-11-02
tags: [seam, build]
description: How build.sex writes the whole site.
---

Normally `seam` turns one file into one document. `build.sex` instead
generates every page itself, with a *formatter macro* to render each one,
and `%write` to save it:

```lisp
(%for post in %posts
  (%write-html (%concat "posts/" (%get slug %post) ".html")
    (%with %post
      (%with (:root "../")
        (%include "post.sex")))))
```

The feed is the same, with `%formatter/xml`, and so is the stylesheet, with
`%formatter/css`. Building the site is then just:

```sh
seam --text build.sex
```
