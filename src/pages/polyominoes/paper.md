---
layout: "../../layouts/Post.astro"
title: "Four-arm polyominoes in Golomb’s hierarchy"
description: "A complete classification with Lean verification. Paper, LaTeX sources, formal proofs, citation, and research history."
updated: 2026-09-11
---

**A complete classification with Lean verification**

Angel Ivanov Raychev · September 2026

**Preprint prepared for submission.** This manuscript has not yet been submitted to arXiv.

[**Read the paper (PDF)**](/polyominoes/four-arm-polyominoes.pdf) · [LaTeX source](/polyominoes/arxiv-source.zip) · [BibTeX citation](/polyominoes/citation.bib)

Start with the [interactive overview](/four-arm-polyominoes/) to try individual shapes. The paper presents the complete theorem and its proofs in a conventional mathematical format. The [expanded proof appendix](/polyominoes/proofs/) provides further coordinate details.

## Abstract

We classify the polyominoes obtained by adjoining four straight arms to a single square, allowing zero arm lengths, according to their ability to tile rectangles, half-strips, bent strips, quadrants, strips, half-planes, and the plane. We also classify their ability to tile an integer enlargement of themselves. Tiles occupy whole square-grid cells; translations, rotations, and reflections are permitted. Exactly five capability profiles occur. For the family $P(n,1,1,0)$, the rectangle profile holds for $n\le3$ and the bent-strip profile, with no half-strip or rep-tiling, for every $n\ge4$. A cross with four positive arms tiles the plane precisely when two opposite arms have length one; it never tiles a half-plane. Explicit periodic constructions and geometric obstructions are combined with finite symbolic case certificates. A Lean 4 development verifies the full classification for every natural four-tuple, including the interpretation of the certificates as statements about arbitrary infinite tilings. The account incorporates the author's 2020–2021 L- and T-polyomino work, reconstructs Dahlke's gun argument, and documents the subsequent AI-assisted proof development and formalization.

## Formal proof

The accepted Lean 4.33.1 development contains **538 source modules**. Its theorem `PolyominoFormal.all_tuples_classified` proves all eight capabilities, positively or negatively, for every tuple of natural arm lengths. It has no remaining obstruction assumptions. Its axiom report lists only `propext`, `Classical.choice`, and `Quot.sound`.

- [Frozen Lean source archive](https://raw.githubusercontent.com/RaychevAngel/angelraychev.com/ec308bfcb092fa71a78cecd991be6e85e5b369b9/public/polyominoes/lean-proofs.zip)
- [Artifact identity, theorem map, and reproduction instructions](/polyominoes/formal-artifact.md)
- [Read the main theorem](/polyominoes/lean/MainClassification.lean)

The paper states the exact square-grid and integer-enlargement conventions. The artifact guide identifies the verified release by commit and checksum. The existing verification receipts are included; manuscript preparation did not change the mathematical sources or repeat the full Lean build.

## Research history and contributions

My original work took place between **October 2020 and March 2021**. It included the L classification and the handwritten T classification apart from $P(4,1,1,0)$ and $P(5,1,1,0)$. The L results were presented in the [January 2021 paper](/polyominoes/raychev-2021-l-quadrant.pdf) and [May 2021 paper](/polyominoes/raychev-2021-l-half-plane.pdf), both in Bulgarian. The presentation dates are distinct from the research period. The handwritten T proofs were not provided to Astra 6; the reconstruction agrees with that earlier classification.

Karl Dahlke's [Gun Theorem, section 23](https://github.com/eklhad/trec/blob/57deb1bdeceff8dda76e4260adcf52fe3a9a901f/theorems/gun) is a direct source for the corner method. It already rules out rectangles for every $P(n,1,1,0)$ with $n\ge4$, including both exceptional cases. The present account reconstructs those cases and establishes the half-strip and integer rep-tile obstructions with explicit progress inequalities and Lean proofs. It makes no claim that those consequences could not be extracted from the earlier argument. Dahlke's theorem is documented by **19 May 2019**; its original composition date is unknown.

The subsequent development used **OpenAI's Astra 6 model, operating through the Codex harness, extensively for mathematical investigation, proof reconstruction and development, constructions, counterexample searches, certificate generation, Lean formalization, and preparation of the manuscript and figures**. The two exceptional cases and the genuine-cross analysis were developed through this investigation. These were substantive contributions, beyond editing. I initiated and directed the investigation and take responsibility for the submitted manuscript. The paper credits earlier authors at the relevant results and does not claim that every ingredient is new.

## Acknowledgments

I am deeply grateful to **Professor Stanislav Harizanov**, my mentor during the original research, for recognizing my potential, offering important advice, and carefully checking my work. I also thank my mathematics teacher **Dimitar Dimitrov**, whose guidance extended far beyond the classroom. As a mentor in life, he helped me find direction, encouraged me to pursue mathematical research, and introduced me to Professor Harizanov. Their encouragement and support were central to the work I undertook between October 2020 and March 2021.

## Suggested citation

Angel Ivanov Raychev. *Four-arm polyominoes in Golomb’s hierarchy: A complete classification with Lean verification*. Preprint, September 2026.

```bibtex
@misc{raychev2026fourarm,
  author = {Raychev, Angel Ivanov},
  title = {Four-arm polyominoes in {Golomb}'s hierarchy:
           A complete classification with {Lean} verification},
  year = {2026},
  month = sep,
  note = {Preprint},
  url = {https://angelraychev.com/polyominoes/paper/}
}
```

An arXiv identifier will be added after an actual announcement. The [paper bibliography](/polyominoes/references.bib) contains the cited original works.
