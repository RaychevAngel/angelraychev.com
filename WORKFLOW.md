# Workflow

How an idea becomes a live page.

## Division of labour

**Angel** generates the ideas and makes the final call on publication. The creative and
lateral work is his: what is worth investigating, which framing is wrong, what question
nobody is asking.

**Claude is the voice.** Claude researches the ideas, critiques them, verifies the
claims, and aggregates them into readable prose. Angel reviews on localhost and says
yes or no.

The loop: Angel gives an idea → Claude researches, critiques, drafts → Angel reads it on
localhost and reacts with more ideas → repeat until Angel says publish.

## The loop

1. **Draft** — straight into this repo, nowhere else.
   - Short piece → `src/content/posts/<slug>.md` with `draft: true`
   - Designed document → `public/reports/<slug>/index.html` + an entry in `src/data/reports.ts`
2. **Preview** — `npm run dev`, <http://localhost:4321>. Nothing is public.
3. **Approve** — Angel reviews on localhost. Yes or no.
4. **Publish** — on a yes: commit and push. Live in ~30 seconds.
5. **Revise** — same loop. Every push redeploys.

## What needs approval, and what does not

| Needs an explicit yes | Claude keeps aligned without asking |
| --- | --- |
| Anything a reader sees: notes, reports, homepage and About copy, titles, descriptions, navigation | Build config, dependencies, the deploy workflow, this document, bug fixes, and keeping local in sync with `origin/main` |

Claude is responsible for local and GitHub never drifting. That is reported after the
fact, not asked about in advance.

## Rules

- **No content ships without an explicit yes.** Publishing is public, gets cached and
  indexed by things nobody controls, and is not cleanly undoable.
- **Drafts are genuinely private, in two different ways.** A note with `draft: true` is
  not built, not listed and not reachable even after pushing. An *uncommitted* report
  exists only on Angel's machine — that is the real gate for designed documents, since
  everything in `public/` goes live the moment it is pushed.
- **The repo is the source of truth.** Claude Artifacts are throwaway previews only,
  never a second copy to maintain. Research digests stay in their own project folders
  and are never bulk-copied here.
- **Claims are verified before they ship.** This is published under Angel's name and the
  site's stated premise is that corrections get published, so the standard is what
  survives checking rather than what sounds right.
- **Rollback is one command:** `git revert HEAD && git push` → live in ~30s.

## Note or report?

- **Note** — prose the site layout can carry: headings, lists, tables, quotes. Markdown.
- **Report** — needs its own design: custom charts, colour that encodes meaning, a
  structure the shell cannot express. Self-contained HTML.

## Away from the Mac

No local preview available. Either Claude publishes a throwaway Artifact to preview, or
pushes to a branch — `main` is the only branch that deploys.
