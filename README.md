# angelraychev.com

Personal site. Astro, static output, deployed on Vercel.

## Writing

Two kinds of content:

- **Notes** — Markdown in `src/content/posts/*.md`, rendered in the site layout.
  Copy `_template.md`, set `draft: false`, and it appears on the index and in the RSS feed.
  Files beginning with `_` are ignored.
- **Reports** — self-contained HTML documents in `public/reports/<slug>/index.html`,
  each with its own design. Register them in `src/data/reports.ts` so they show on the index.

## Local

```bash
npm install
npm run dev      # http://localhost:4321
npm run build    # -> dist/
```

Deploys automatically on push to `main`.
