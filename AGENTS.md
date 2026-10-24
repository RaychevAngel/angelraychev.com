# Portfolio maintenance

Use `docs/PUBLICATION-STANDARD.md` for publication and resource presentation.
`src/data/publications.json` is authoritative for work identities, overview URLs,
resource types, publication records and selected PDF versions. Use the shared
header/resources components; do not add ad hoc primary link rows in article prose.

Keep PDF, Code, Lean semantics and ordering exact. arXiv and Journal are publication
records, not PDF aliases. Preserve public/private implementation boundaries and
formalization scope. Existing archive URLs and frozen artifact identities must
remain available.

Research owners control mathematical claims, authorship, manuscript generators,
PDFs, proof sources and status. Presentation changes must preserve their work and
concurrent edits. Do not replace shared website files wholesale from stale exports.
Update registry metadata when an authorized publication/status change occurs.

Before publication run `npm run test:publications`, `npm run test:math`,
`npm run test:tables`, and `npm run build`; then visually inspect changed layouts
and verify the live deployment. Build success is not visual or scientific proof.
