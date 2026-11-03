# A blog in seam

A small but complete blog, built from the ideas in [`../blog-concept`](../blog-concept):
a shared layout, posts listed on an index by date, a tags page and an RSS feed.

```sh
cd samples/blog
seam --text build.sex   # Writes the site into public/.
```

- `site.sex` defines everything shared: the site's details, `%posts` (every
  post's frontmatter, without drafts, newest first) and the `%page` layout.
- `posts/*.md` are the posts, in Markdown with YAML frontmatter
  (`title`, `date`, `tags`, `description`, and `draft: true` to leave one out).
  Markdown is literate, so posts may call macros, e.g. `(%length %posts)`.
- `index.sex`, `tags.sex` and `feed.sex` are pages, which can each be rendered
  alone (`seam --html index.sex`, `seam --xml feed.sex`), while `post.sex`
  renders a post given its details by `%with`.
- `build.sex` renders every page with a formatter macro
  (`%formatter/html :document true ...`) and saves it with `%write`.
- `style.sex` is the stylesheet, in seam's CSS syntax.

Paths (`%glob`, `%write`) are relative to the working directory, so run
`seam` from this directory.
