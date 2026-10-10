# angelraychev.com — handoff

Everything needed to work on this site from scratch, on any machine. Read this first.

## What it is

The personal site of **Angel Ivanov Raychev**. Long-form written investigations,
currently on physical capability and aging, but the site is deliberately **not scoped to
a topic** — Angel intends to write about a wide range of subjects, and any copy that
narrows the site to one field has been removed on purpose. Do not reintroduce a tagline,
an About page, or a scoping description.

It is a reading site for essays and living research/development projects.

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

Astro 7, static output, zero client-side JavaScript. Markdown and KaTeX render the
prose and formulas. No CSS framework or UI library. Node 22+.

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

**Planned pieces** are a source-only string array in `src/pages/index.astro` (`const ideas`).
They are not displayed. To publish one, write the Markdown file, add its group entry,
and remove the corresponding backlog string.

The homepage groups published articles under **AI and machine learning**, **Mathematics**,
**Human agency**, and **Running**, in the explicit reading order in `src/pages/index.astro`. Each
article has one entry; papers and supporting project pages remain beneath that entry.
Each entry shows only its linked title and date, with no subtitles or descriptions.
When publishing an article, assign its URL to a group; a build check prevents missing or
duplicate entries. The ideas array is a source-only backlog, not displayed on the site.

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
- **No nav, no About page, no tagline, no cards or filters.** On 13 September 2026,
  Angel approved three plain subject headings, then removed the article labels.
  Keep only linked titles and dates under each heading; no subtitles or descriptions.
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

## Running content

The running section has three main entries:

- `running-notebook.md`: the living 800–5000 m project, goals, current programme,
  progression gates and decisions.
- `what-should-a-running-workout-maximize.md`: the scientific argument and explicitly
  proposed exposure models, with primary references.
- `running-makes-the-city-smaller.md`: the personal essay about running and mobility.

The supporting running record starts at `/running/record/`. Its six period chapters
are Markdown in `src/data/running/periods/`, rendered by
`src/pages/running/record/[period].astro`. A chapter opens with a readable account
and selected dated notes. `RunLedger.astro` adds expandable monthly tables beneath
it, using the minimal public `src/data/running/recorded-runs.json` register. Separate
warm-up, workout and cool-down uploads remain separate records; never treat the
upload count as a count of physical sessions.

`/running/record/results/` uses `src/data/running/race-results.json` for source-linked
race history and `src/data/running/personal-bests.json` for the single canonical
best-mark table. Keep personal-best summary tables on this page; the notebook
links to it and keeps the goal profile and current interpretation. A meaningful
dated account can still state its own result. Original best times/distances,
race/training type, supported date basis and source stay visible. For an
untabulated distance, score the same pace over the closest shorter listed event,
including the mile when it is the nearest one; mark the score as derived and
show its scored distance/time. Do not invent a score below the table's shortest
distance. Derived comparisons do not establish additional achieved PBs. Pin the
table edition, apply the lower-score rule and keep timing/course uncertainty
beside the reference. Approximate marks must not become exact times or points.
The current programme lives at `/running/record/2026/programme/`;
the recovered historical sheet is at `/running/record/2022/programme/`. These are
supporting pages, not additional homepage articles or RSS entries. Keep the three
main reading paths and the existing child-page pattern.

`src/pages/running-notebook/log.md` retains `/running-notebook/log/` and all 28
previous heading IDs as links into the new record. Preserve those IDs and the
period chapter IDs when refining prose; old bookmarks should remain useful.

For a new session, update its dated chapter note first, then the current notebook
only when the result changes the interpretation or next decision. Add an upload
to the register when source material establishes it. Use its supported local date;
retain and label UTC when no local date is established. Preserve the source's
displayed distance and moving time without rescaling them into an intended track
distance or race result. Zero-distance uploads are retained with a displayed dash.
Keep original files, GPS, sensor streams, complete descriptions and provenance
outside the public repository.

Each results row links its time to the primary result and its date to the fuller
account. Keep heat places separate from combined classifications, and chip, gun,
moving and elapsed times distinct. An organizer's course label is not an added
certification claim. Corrections should remain intelligible in the dated account.

New months and ordinary cycles stay inside the relevant period. Start another
chapter when the purpose or training phase materially changes. Before replacing a
programme, preserve its dated version and keep the governing plan identifiable
from the corresponding session notes. Completed training and planned transitions
must remain separate, including when a planned session's date has already passed.

Review the chapter's organization once it approaches twenty full dated session
notes or 4,000 words of prose. This is an editorial review trigger, not an automatic
page split. Routine repeats can retain exact work, rest and splits with one useful
observation; the front chronology and comparisons should emphasize checkpoints.
If a year genuinely needs several phase chapters, keep its year page as a concise
contents page and preserve old session fragments as links to their new homes.
`RunLedger.astro` currently filters by year only: add supported date bounds or
explicit membership before splitting one year across chapters, so uploads appear
once rather than being duplicated in every phase. Do not create empty future pages.

The initial publication on 9 October 2026 includes completed sessions through
8 October. When updating, keep future plans distinct from completed work, preserve
the conditions behind workout comparisons, and leave historical observations available
when the current programme changes. The LT and VO₂ ladders advance independently;
each target is a graduation gate, not a compulsory first pace for the next structure.
The physiological labels name intentions, not measurements inferred from split times.
Do not publish the underlying chat archive or private research digests.

The notebook's organizing ambition is 800+ World Athletics points across each
listed 800–5000 m event, initially an equal 810-point curve. Keep numerical scores
with the goal marks and meaningful historical/event comparisons. Pin the men's
outdoor table edition and apply its lower-score lookup rule between thresholds;
do not confuse table points with world-ranking points, age grading or a population
percentile. A rarity claim needs a named population, year and complete enough
denominator. Different historical dates do not form a simultaneous fitness curve.

Longer repetitions and continuous efforts need per-kilometre pace beside their
times. Short fast repetitions can stay split-focused. Pace from intended work
distance is separate from a whole recording's moving-time/recorded-distance pace,
which may include recoveries. Keep estimated distances/times and nominal laps
labelled. Elevation gain and surface matter for hilly outings; vertical range is
not ascent. Grade-adjusted pace needs an identified model or source and remains
an estimate, not an inferred flat race result.

## Current state

As of 9 October 2026, ten homepage entries are grouped by subject. The index
combines published Markdown articles with the princess and cop-prisoner project pages.
The source-only ideas backlog remains hidden.

Three earlier articles (`longevity-matrix`, `capability-stack`, `accumulation-decade`)
and an About page were removed in the September 2026 rebuild. Recoverable from git
history. Their old URLs now 404.

Research digests backing the writing live only on Angel's machine, outside this repo, at
`~/personal-projects/athleticism/research/`. They are source material, not published, and
are not available to you unless Angel shares them.
