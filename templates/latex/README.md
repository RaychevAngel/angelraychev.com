# Shared manuscript presentation

`angel-publication` v1.0 is the common layout foundation for actively maintained
reports and new manuscripts. It does not change scientific notation or content.
Published journal PDFs, frozen arXiv versions, historical reports and the two
currently active mathematical manuscripts retain their existing identity.

## Start a manuscript

Copy this directory into a new project. Replace the specimen content, title,
author, dates, status, running title, URLs and example bibliography. Keep
`\documentclass[11pt,letterpaper]{article}` and load the style last, after any
manuscript-specific packages and macros.

Build with a local TeX installation providing pdfLaTeX, BibTeX and latexmk:

```sh
python3 build-publication.py manuscript.tex --output build
```

The helper performs no network/model calls. It compiles and checks the log,
then records input/output hashes. Rendering and page-by-page visual review remain
separate acceptance steps. All required packages are declared in the style;
the specimen additionally uses natbib.

## Resource links

Use `\PublicationLinks[Lean URL]{Overview URL}{Code URL}` in front matter.
The order is Overview, Code, Lean; empty resources and separators disappear.
Omit the optional brackets when there is no Lean guide. Use `{}` for no Code:

```tex
\PublicationLinks{https://angelraychev.com/project/}{}
\PublicationLinks[https://angelraychev.com/project/lean/]
  {https://angelraychev.com/project/}{}
```

Overview opens the main website page, Code the relevant public repository, and
Lean the human-readable scope/reproduction guide. A PDF does not need a link to
itself. The website registry owns the corresponding public destinations.

## Layout and mathematical objects

`\PublicationTitleFont` owns title typography for manual title blocks and the
standard article `\maketitle`; subtitles remain normal weight. One-inch margins,
Latin Modern text/math, consistent headings, captions,
booktabs tables, links, running headers and page numbers are shared. AMS theorem,
lemma, proposition, corollary, definition, example and remark environments use a
common section counter unless the manuscript already defines them. Existing
environments are preserved. Use `\label`, `\eqref` and typed `\cref` references;
do not hard-code object numbers. Prefer AMS `proof` and `\qedhere` for a proof
ending in a display. Use `aligned`, `split` or `multline` for long equations.

Use `publicationdiagram` only around a diagram that exceeds the text width. It
shrinks proportionally and never enlarges; keep the caption outside. Do not scale
body text or equations to conceal an overflow.

## Adopt an existing report

Preserve the original source/PDF and hashes first. Retain content-specific macros,
all scientific statements, equations, results, figures, citations and authorship.
Load the style last; name a dated presentation revision separately from the
original paper/report date. Include the exact style copy in the source archive,
so the archive builds independently of a moving website checkout.

Require clean compilation, no unresolved/duplicate references or citations, no
missing glyphs or overfull boxes, embedded fonts and valid internal PDF targets.
Compare the scientific source after explicitly documented layout wrappers; hash
unchanged assets. Render and inspect every page. A template migration is not a new
experiment, scientific result, submission or publication version.

The search and hindsight reports adopt this style as 24 October 2026 presentation
revisions. Their version records preserve the original layouts and hashes.
