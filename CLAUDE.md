# angelraychev.com — handoff

Everything an agent needs to work on this site. Read this before touching anything.

## What it is

The personal site of **Angel Ivanov Raychev**. Long-form written investigations,
currently on physical capability and aging, but the site is deliberately *not* scoped to
a topic — Angel intends to write about a wide range of subjects and any copy that
narrows the site to one field has been removed on purpose. Do not reintroduce a tagline,
an About page, or a description that scopes it.

It is a reading site. One article exists so far, plus a public list of planned pieces.

## Where everything lives

| | |
| --- | --- |
| Source | `~/personal-projects/angelraychev.com` |
| Repo | `github.com/RaychevAngel/angelraychev.com` — **public** |
| Hosting | GitHub Pages, deployed by GitHub Actions on push to `main` |
| Domain | `angelraychev.com`, registered at GoDaddy, expires Feb 2029 |
| DNS | GoDaddy nameservers `ns29/ns30.domaincontrol.com` |
| Apex records | Four A records → `185.199.108–111.153` |
| `www` | CNAME → `raychevangel.github.io` (301s to apex) |
| Second domain | `araychev.com` — GoDaddy 301 forward to the apex. Angel owns both. |
| TLS | Let's Encrypt via GitHub Pages, HTTPS enforced |
| Contact | `angel.ivanov.raychev@gmail.com` (in the footer, site-wide) |

Vercel is **not** an option: the connector only sees Angel's `SynthLabs` work team and
returns 403 on project creation there. Don't retry it without a personal account.

## Stack and commands

Astro 7, static output, zero client-side JavaScript. No CSS framework, no UI library,
no dependencies beyond Astro itself.

```bash
npm install
npm run dev      # http://localhost:4321  — Angel reviews here
npm run build    # → dist/
```

`npx astro dev stop` stops a backgrounded dev server. **Restart the dev server after
changing `src/content.config.ts`** — collection config is cached and stale content will
silently not appear.

## Content model

One content type. There is no notes/reports split any more — it existed and was removed
for simplicity. Do not reintroduce it.

An article is a Markdown file at `src/content/posts/<slug>.md`, served at `/<slug>`.

```yaml
---
title: "Configuration and Consumption"
description: "One sentence. Used for meta tags and RSS."
updated: 2026-09-03
draft: true      # optional; drafts are not built, not listed, not reachable
---
```

Files beginning with `_` are ignored by the loader. `draft: true` is a genuine gate —
the page is not generated at all.

Planned pieces are a plain string array in `src/pages/index.astro` (`const ideas`). They
render as unclickable grey rows labelled `idea` where the date normally sits. Titles are
sentence case. To publish one, write the Markdown file and delete the string.

The homepage sorts everything **alphabetically** — articles and ideas mixed together.
Articles are links with a date; ideas are grey text with the word `idea`.

## Style and theme

Angel asked repeatedly for maximum minimalism. The brief, in his words: *"the most
minimalistic website you can imagine"*, *"everything is black and white, mostly with a
white background"*, *"more robotic, more modernistic, a little bit more coding-style"*,
*"I just imagine it as a book, which is just text."*

- **Monospace throughout.** `ui-monospace, "SF Mono", SFMono-Regular, Menlo,
  "Cascadia Mono", "Roboto Mono", Consolas, monospace`. No second typeface anywhere.
- **Pure black on pure white.** `--fg: #000`, `--bg: #fff`. One grey (`--dim: #767676`)
  for de-emphasis and one hairline (`--rule: #ddd`). **There is no accent colour and
  none should be added.**
- **Single theme by design.** No dark mode. This was a deliberate decision, not an
  omission — do not add `prefers-color-scheme` blocks.
- Body 14.5px / line-height 1.8, measure capped at 660px.
- Links are underlined; hover inverts to white-on-black.
- No nav, no About page, no tagline, no descriptions on the index, no category chips.
  Each of these existed and was deliberately removed.
- Plots are allowed but must be black and white and minimal. The one in the current
  article is hand-written inline SVG using only `#000` and `#767676`.

All tokens live at the top of `src/styles/global.css`.

## Layout of the source

```
src/
  content/posts/*.md          articles
  content.config.ts           collection schema (title, description, updated, draft)
  layouts/Base.astro          shell: header, footer, <head>. `home` prop makes the
                              name an <h1> on the index and a link elsewhere
  layouts/Post.astro          article wrapper: title + date
  pages/index.astro           the index, and the `ideas` array
  pages/[...slug].astro       article routes at the site root
  pages/rss.xml.ts            hand-rolled RSS, no dependency
  styles/global.css           the entire stylesheet
public/
  CNAME                       angelraychev.com
  robots.txt
```

## Workflow — read this part carefully

The division of labour is Angel's own and he was explicit about it:

> *"You are the voice. I make the ideas. I give ideas, you research them, you critique
> them, and you aggregate them by means of text. I look, and I give more ideas. My task
> is the creative part, the thinking outside the box. Your part is aggregating my
> thoughts into readable pieces."*

So: **Angel supplies ideas and holds the publication gate. The agent researches,
critiques, verifies and writes the prose.** Site copy is not placeholder text awaiting
Angel's rewrite — the agent is the author. He reviews on localhost and says yes or no.

**The loop:** draft into the repo → `npm run dev` → Angel reviews at localhost:4321 →
on an explicit yes, commit and push → live in ~30 seconds.

**What needs an explicit yes:** anything a reader sees — articles, index entries,
homepage copy, titles, the ideas list.

**What the agent keeps aligned without asking:** build config, dependencies, the deploy
workflow, this file, bug fixes, and keeping local in sync with `origin/main`. Reported
after the fact. The agent is responsible for local and GitHub never drifting.

**Rollback:** `git revert HEAD && git push` → back in ~30 seconds.

## Editorial standard

Angel's stated premise is that claims should be checked and corrections published. The
existing article ends with a section listing what did not survive verification,
including citation errors found in the research behind it. Keep that standard: verify
headline numbers against primary sources, label what is literature versus anomaly versus
practitioner claim, and publish the corrections rather than quietly fixing them.

Angel also pushed back on framing every piece as a thought experiment — a blanket
epistemic label is restrictive and becomes false the day an actual experiment happens.
Epistemic status belongs in the prose of the piece that needs it, not as site furniture.

## Gotchas already hit

- **GitHub only requests the TLS certificate after its own DNS health check passes, and
  that check does not re-run automatically after propagation.** If a certificate is
  stuck, force it: `gh api -X PUT repos/RaychevAngel/angelraychev.com/pages -f cname=""`
  then set it back to `angelraychev.com`. The cert issued within a minute of doing that.
- **`gh api -f https_enforced=true` sends the string `"true"` and silently fails.** Use
  `-F https_enforced=true`.
- **GitHub Pages does not read `CNAME` from the build artifact** when deploying via
  Actions. The custom domain must be set through the API or repo settings.
- **The CDN holds pages for `max-age=600`.** After a push, the live site can serve the
  previous build for up to ten minutes even though the deployment succeeded. Check
  `last-modified`, not just the workflow conclusion.
- **Astro's dev server does not resolve `/dir/` to `/dir/index.html` for files in
  `public/`,** while real static hosts do. If static HTML is ever served from `public/`
  again, dev will 404 where production works.

## Current state

One published article: `configuration-and-consumption`. Fourteen ideas listed. Three
earlier articles (`longevity-matrix`, `capability-stack`, `accumulation-decade`) and an
About page were deleted in the September rebuild — recoverable from git history if
wanted. Their old URLs now 404.

Research digests backing the work live outside this repo, in
`~/personal-projects/athleticism/research/`. They are source material and are not
published.
