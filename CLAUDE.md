# angelraychev.com — handoff

Everything needed to work on this site from scratch, on any machine. Read this first.

## What it is

The personal site of **Angel Ivanov Raychev**. Long-form written investigations,
currently on physical capability and aging, but the site is deliberately **not scoped to
a topic** — Angel intends to write about a wide range of subjects, and any copy that
narrows the site to one field has been removed on purpose. Do not reintroduce a tagline,
an About page, or a scoping description.

It is a reading site. One article exists so far, plus a public list of planned pieces.

Live at <https://angelraychev.com>.

## Access you need

| For | What | Who grants it |
| --- | --- | --- |
| Reading the code | Nothing — the repo is public | — |
| Publishing | Collaborator push access on the repo | Angel, via GitHub repo settings |
| DNS or domain changes | GoDaddy account login | Angel only — do not ask for credentials |

You do **not** need hosting credentials. Deployment is automatic from `main`.

## Get it running

```bash
git clone https://github.com/RaychevAngel/angelraychev.com.git
cd angelraychev.com
npm install
npm run dev      # http://localhost:4321
npm run build    # → dist/
```

Astro 7, static output, zero client-side JavaScript. No CSS framework, no UI library, no
dependencies beyond Astro itself. Node 22+.

**Restart the dev server after changing `src/content.config.ts`** — collection config is
cached, and stale content silently fails to appear. `npx astro dev stop` stops a
backgrounded server.

## Where it is hosted

| | |
| --- | --- |
| Repo | `github.com/RaychevAngel/angelraychev.com` (public) |
| Hosting | GitHub Pages, built by GitHub Actions on every push to `main` |
| Deploy time | ~30 seconds |
| Domain | `angelraychev.com`, GoDaddy, expires Feb 2029 |
| DNS | GoDaddy nameservers `ns29`/`ns30.domaincontrol.com` |
| Apex | Four A records → `185.199.108.153`, `.109.153`, `.110.153`, `.111.153` |
| `www` | CNAME → `raychevangel.github.io`, 301s to apex |
| Second domain | `araychev.com` — GoDaddy 301 forward to apex. Angel owns both. |
| TLS | Let's Encrypt via GitHub Pages, HTTPS enforced |
| Contact shown | `angel.ivanov.raychev@gmail.com`, footer, site-wide |

Vercel is not an option: its connector only sees Angel's `SynthLabs` work team and
returns 403 on project creation there.

## Content model

One content type. There was previously a notes/reports split; it was removed for
simplicity. Do not reintroduce it.

An article is a Markdown file at `src/content/posts/<slug>.md`, served at `/<slug>`.

```yaml
---
title: "Configuration and Consumption"
description: "One sentence. Used for meta tags and RSS."
updated: 2026-09-03
draft: true      # optional; drafts are not built, not listed, not reachable
---
```

Files beginning with `_` are ignored by the loader. `draft: true` is a real gate — the
page is not generated at all, so it is safe to commit and push a draft.

**Planned pieces** are a plain string array in `src/pages/index.astro` (`const ideas`).
They render as unclickable grey rows labelled `idea` where the date normally sits.
Sentence case. To publish one, write the Markdown file and delete the string.

The homepage sorts everything **alphabetically**, articles and ideas mixed. Articles are
links with a date; ideas are grey text with the word `idea`.

## Style and theme

Angel asked repeatedly for maximum minimalism. In his words: *"the most minimalistic
website you can imagine"*, *"everything is black and white, mostly with a white
background"*, *"more robotic, more modernistic, a little bit more coding-style"*, *"I
just imagine it as a book, which is just text."*

- **Monospace throughout.** `ui-monospace, "SF Mono", SFMono-Regular, Menlo,
  "Cascadia Mono", "Roboto Mono", Consolas, monospace`. No second typeface anywhere.
- **Pure black on pure white.** `--fg: #000`, `--bg: #fff`, one grey `--dim: #767676`
  for de-emphasis, one hairline `--rule: #ddd`. **There is no accent colour and none
  should be added.**
- **Single theme by design. No dark mode.** A deliberate decision, not an omission — do
  not add `prefers-color-scheme` blocks.
- Body 14.5px, line-height 1.8, measure capped at 660px.
- Links underlined; hover inverts to white-on-black.
- **No nav, no About page, no tagline, no index descriptions, no category labels.** Each
  of these existed and was deliberately removed.
- Plots are allowed but must be black and white and minimal. The one in the current
  article is hand-written inline SVG using only `#000` and `#767676`.

All tokens are at the top of `src/styles/global.css`.

## Source layout

```
src/
  content/posts/*.md      articles
  content.config.ts       schema: title, description, updated, draft
  layouts/Base.astro      shell: header, footer, <head>. A `home` prop makes the
                          name an <h1> on the index and a link elsewhere
  layouts/Post.astro      article wrapper: title + date
  pages/index.astro       the index, and the `ideas` array
  pages/[...slug].astro   article routes at the site root
  pages/rss.xml.ts        hand-rolled RSS, no dependency
  styles/global.css       the entire stylesheet
public/
  CNAME                   angelraychev.com
  robots.txt
```

## Workflow

The division of labour is Angel's own, stated explicitly:

> *"You are the voice. I make the ideas. I give ideas, you research them, you critique
> them, and you aggregate them by means of text. I look, and I give more ideas. My task
> is the creative part, the thinking outside the box. Your part is aggregating my
> thoughts into readable pieces."*

**Angel supplies ideas and holds the publication gate. You research, critique, verify and
write the prose.** Site copy is not placeholder text awaiting his rewrite — you are the
author. He reviews on localhost and says yes or no.

**The loop:** draft into the repo → `npm run dev` → Angel reviews at `localhost:4321` →
on an explicit yes, commit and push → live in ~30 seconds.

**Needs an explicit yes:** anything a reader sees — articles, index entries, homepage
copy, titles, the ideas list.

**Keep aligned without asking:** build config, dependencies, the deploy workflow, this
file, bug fixes, and keeping local in sync with `origin/main`. Report after the fact. You
are responsible for local and GitHub never drifting.

**Rollback:** `git revert HEAD && git push` → back in ~30 seconds.

## Editorial standard

Angel's stated premise is that claims get checked and corrections get published. The
existing article ends with a section listing what did not survive verification, including
citation errors found in the research behind it. Keep that standard: verify headline
numbers against primary sources, distinguish peer-reviewed evidence from outlier cases
and practitioner claims, and publish corrections rather than quietly fixing them.

Angel pushed back on labelling every piece a thought experiment — a blanket epistemic
disclaimer is restrictive and becomes false the day a real experiment happens. Epistemic
status belongs in the prose of the piece that needs it, not as site furniture.

## Gotchas already hit

- **GitHub only requests the TLS certificate after its own DNS health check passes, and
  that check does not re-run automatically after DNS propagates.** If a cert is stuck,
  force a recheck: `gh api -X PUT repos/RaychevAngel/angelraychev.com/pages -f cname=""`
  then set it back to `angelraychev.com`. The cert issued within a minute of that.
- **`gh api -f https_enforced=true` sends the string `"true"` and silently fails.** Use
  `-F https_enforced=true`.
- **GitHub Pages does not read `CNAME` from the build artifact** when deploying via
  Actions. The custom domain must be set through the API or repo settings.
- **The CDN caches for `max-age=600`.** After a push the live site can serve the previous
  build for up to ten minutes even though the deployment succeeded. Check the
  `last-modified` header, not just the workflow's green tick.
- **Astro's dev server does not resolve `/dir/` to `/dir/index.html` for files in
  `public/`,** while real static hosts do. Relevant if static HTML is ever served from
  `public/` again — dev will 404 where production works.

## Current state

One published article: `configuration-and-consumption`. Fourteen ideas listed.

Three earlier articles (`longevity-matrix`, `capability-stack`, `accumulation-decade`)
and an About page were removed in the September 2026 rebuild. Recoverable from git
history. Their old URLs now 404.

Research digests backing the writing live only on Angel's machine, outside this repo, at
`~/personal-projects/athleticism/research/`. They are source material, not published, and
are not available to you unless Angel shares them.
