# Math typesetting: one implementation, explicit release checks

The site uses the shared renderer in `src/lib/math.mjs`. Markdown math, direct
Astro equations and imported/pre-rendered proof text must produce the same KaTeX
HTML, MathML and source annotations. The renderer, its stylesheet and its local
font files are a versioned unit. Updating one without the others is not safe.
All explicitly math-specific styling belongs in `src/styles/math.css`. The source
gate checks CSS rules and Astro/Markdown `<style>` blocks for math selectors and
rejects overrides elsewhere. JavaScript DOM queries, comments, ordinary CSS
declarations and Markdown code examples are not treated as stylesheets.

## Mechanical release gate

Run from the repository root:

```sh
node scripts/math-audit.mjs --dependencies-only
node --test scripts/math-audit.test.mjs
npm run build
node scripts/math-audit.mjs
```

The deployment workflow must run these checks before uploading the Pages artifact.
`node scripts/math-audit.mjs --json` provides the complete route inventory and
issues for a release receipt. `--dist /absolute/build/output` checks an alternative
build directory.

The audit checks every emitted `.html` file, including files copied from `public/`,
not only the page being edited. It resolves KaTeX from its actual callers and
rejects mismatched or unpinned versions. For each equation it requires accessible
MathML and the original TeX source, and compares the output with a fresh rendering
through the current shared implementation. This catches stale pre-rendered HTML,
not merely parser errors. Math pages must load local math CSS; referenced local CSS
assets must exist, and math fonts may not silently depend on a remote CDN.
Referenced KaTeX font files are also hash-checked against the installed renderer's
font distribution, so an empty, damaged or substituted font file is not a pass.
A bounded raw-delimiter check also rejects typical unprocessed `$P$`, `$M=4$`
or `$$...$$` notation in rendered prose/captions, while excluding code, scripts,
styles and normal currency such as `$10/$20`. This is deliberately a conservative
alarm, not an attempt to infer every possible mathematical phrase from prose.
Literal examples of delimiter syntax belong in code formatting.

Tests deliberately corrupt sizing classes, vertical positioning, source and
accessibility markup. These failures must remain failures. A successful Astro
build by itself is not sufficient evidence of correct math typesetting.

## Browser release gate

Use the supported computer-use browser, not an alternative automation driver.
The function exported by `scripts/math-browser-check.mjs` is a read-only DOM probe;
`node scripts/math-browser-check.mjs --print` prints its evaluation expression.
Run it on the typography fixture and representative real math pages after fonts
have loaded. It reports equation geometry, missing source/accessibility output,
legacy classes, vertical display clipping, page overflow and used math-font
readiness. Font readiness is an additional check, not proof that every intended
font request succeeded. Restricted browser bridges may not expose FontFaceSet;
the result then explicitly records `fontCheckAvailable: false`, not a claimed
font pass. The default compact result limits returned formula/issue examples but
counts every inspected equation and issue. Use `{ compact: false }` only when the
full diagnostic payload is needed.

Fixture wrappers marked `data-math-probe="subscript"` and
`data-math-probe="superscript"` should contain respectively `x_i` and `x^2`.
The probe requires a smaller, lower subscript and a smaller, higher superscript.
Do not apply those simple geometric assumptions to arbitrary nested expressions
or operator limits.

Review actual screenshots in light and dark themes at a narrow 320-pixel viewport
and a desktop viewport. Initially check Safari and Chromium, browser zoom and print
output as well. Preserve approved screenshots as release evidence; never update a
visual baseline merely to make a failing comparison pass. Reviewers should inspect:

- Inline baseline and punctuation, nested sub/superscripts and readable spacing.
- Fractions, radicals, accents, large delimiters and sum/integral limits.
- Cases, aligned equations and matrices, including tall content without clipping.
- Long equations: deliberate line breaks where helpful; otherwise readable,
  keyboard-accessible horizontal scrolling, never arbitrary shrinking or glyph wrap.
- Real proof pages and the reported context-distillation equation, not only synthetic
  examples. All rendering entry paths must be represented.

An equation's semantic content must remain intact when its layout changes. Do not
replace mathematical notation with approximate Unicode/plain-text imitations or
formula-specific positioning offsets to hide an engine mismatch.

## Scope and limitations

Mechanical checks and screenshots are complementary. Neither establishes that an
author's formula is mathematically correct. Browser font rasterization also differs
slightly across platforms, so acceptable baselines require judgment rather than a
promise of identical pixels on every possible device. Existing PDF manuscripts use
their own TeX/PDF pipeline; fixing website HTML must not silently alter those papers.
