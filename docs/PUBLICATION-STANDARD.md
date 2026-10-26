# Publication and resource standard

## One identity per work

`src/data/publications.json` is the source of truth for portfolio work identities,
overview routes, authors, publication records and resource destinations. The
homepage, article header, supporting resource section and resume generator read
this registry. Do not maintain parallel URL lists in those surfaces.

`title` is the website overview's display title; `manuscriptTitle` is the exact
selected manuscript title for scholarly metadata. They need not be identical.
`manuscriptDate` records its actual date, not the article's last update. Preserve
full author names and manuscript identity when an overview uses an informal title.
Only an explicit `manuscriptModified` may date a change to that manuscript;
updating the website exposition must not imply a modification of a frozen paper.

The registry includes main works, separately identified companions and frozen
archives. A subsection project may have an overview fragment instead of a new
page. Never attach a main manuscript's links automatically to every descendant
route: proofs, guides, companions and historical archives are different objects.

## Exact resource meanings

| Label | Destination |
| --- | --- |
| Linked project title | The main website overview |
| PDF | The actual selected manuscript/report PDF |
| Code | The relevant public project repository |
| Lean | Human-readable formalization scope and reproduction guide |
| arXiv | Abstract and version-history record at `/abs/` |
| Journal | DOI/publisher publication record |
| LaTeX | Buildable manuscript sources, not training implementation |
| Citation | Citation text or a BibTeX entry for this work |

Primary labels and order are fixed: **PDF, Code, Lean**. Omit resources that do
not exist. A guide may link to a raw Lean archive, but the primary Lean link must
not open an unexplained ZIP. Code must not mean a specific pull request, binary
release, foundational third-party project, or this entire website repository.
Describe analysis-only or incomplete reproduction scope in the resource note.

## Page hierarchy

Every registered main/companion/archive page uses the shared `Post` layout:

1. Title.
2. Authors when established.
3. Work type and status, with linked arXiv and Journal records when available.
4. Fixed-order primary resource row, followed by a Resources jump link. If no
   primary artifact exists, Resources alone still makes the supporting material
   discoverable without scrolling through the entire article.
5. Selected PDF version and consequential Code/Lean scope notes.
6. Article update date and substantive content.
7. Generated Resources section for supporting material.

Do not add a hand-written competing button/link row in the article body.
Contextual citations within prose are fine. Related articles and proof navigation
remain meaningful reading links, not alternative names for the primary resources.

LaTeX, citation, documentation, releases, data, evidence, supplementary works and
historical versions belong under Resources. Descriptive labels distinguish
different documents within a category. A bibliography of cited works is not the
same thing as a BibTeX citation for the project itself.

On the homepage, AI and Mathematics entries contain only one linked title and
the quiet article-update date. Titles open the website overview; publication
status, subtitles and PDF/Code/Lean or record links stay on the destination page.
Entries may wrap naturally on small screens. Other homepage sections keep their
own presentation.

On the resume, project titles also link to their website overview, followed by
the available PDF/Code/Lean links in that order. A publication venue may link to
its publication record. Preserve title typography and hierarchy; making a heading
a link is not a reason to shrink it to resource-link text size.

## Canonical manuscript and versions

For an arXiv manuscript, use a direct, version-pinned `/pdf/IDvN` URL as PDF and
the `/abs/ID` record as arXiv. For works without arXiv, use the selected website
PDF. Do not send PDF to an abstract page, journal landing page or paywall.

The selected version must be identified in the registry and must match the
article's scientific account. Preserve prior copies and their hashes as archives,
not as multiple competing primary PDFs. A website revision newer than arXiv must
be named as such. Never infer byte identity between local and arXiv files merely
because they came from related sources. Preserve publisher versus author-preprint
identity; do not relabel the Descent Polynomials preprint as the journal PDF.

The old `/research/generative-reward-models/` route redirects to its main article;
old PDF and reader URLs remain available. Mathematical resource/history pages
remain useful supporting destinations but are no longer competing main hubs.

## Manuscript typography

Maintained reports use the shared house LaTeX foundation under `templates/latex/`:
11-point single-column text, one-inch margins, Latin Modern text/math, consistent
AMS theorem/proof and cross-reference conventions, captions, tables, hyperlinks
and bibliography. The structure of a mathematical paper and an engineering report
need not be identical. Preserve notation, scientific statements and attribution.

Published journal PDFs, frozen arXiv versions, original student/conference reports
and historical archives keep their original identity and typography. A new
presentation revision is named explicitly; it is not a new experiment or an arXiv
revision. Include the pinned house style inside each source bundle so it compiles
independently of this website.

Two active math chats retain responsibility for capture-time and guaranteed-
delivery research, source generators, manuscripts, proofs and research status.
Shared presentation work must not silently rewrite those artifacts or interrupt
the research. Their future exports should preserve the common registry/layout
and update relevant publication metadata deliberately when status changes.

## Update and verification workflow

1. Update the relevant registry entry. Verify public availability and ownership;
   never turn a private implementation into a public Code promise.
2. Update the manuscript/source release and hashes when the selected artifact
   changes. Preserve immutable prior releases. Maintained report entries identify
   an `artifactManifest`; the build checks its PDF/source hashes against the files.
3. Run `npm run test:publications`, `npm run test:math`, `npm run test:tables`,
   and `npm run build`. The build validates destinations, labels, ordering,
   headers, local anchors and supporting-resource sections.
4. Rebuild the resume from its `work_id` entries against this registry. Check PDF
   and Word hyperlink parity, two-page layout, and visual rendering of every page.
5. Visually review changed website pages in desktop/mobile and light/dark modes.
   Automated HTML checks do not establish visual quality or scientific validity.
6. Publish scoped changes without overwriting concurrent work. Verify the live
   deployment and actual resource destinations.
