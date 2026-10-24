import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { renderMath, rerenderMathHtml } from "../src/lib/math.mjs";
import { inspectMathMarkup, auditBuild, findRawMathText, inspectMathCssOwnership } from "./math-audit.mjs";

test("shared output is accepted across demanding inline and display notation", () => {
  const sources = [String.raw`x_{i_j}^{n+1}`, String.raw`\frac{a+b}{\sqrt{c}}`,
    String.raw`\begin{cases}x^2,&x\ge0\\-x,&x<0\end{cases}`,
    String.raw`\begin{aligned}\delta_t&=\log\pi_T(a_t\mid q,c,a_{<t})\\&\quad-\log\pi_{\mathrm{rollout}}(a_t\mid q,a_{<t}).\end{aligned}`];
  for (const displayMode of [false, true]) {
    const html = sources.map((source) => renderMath(source, { displayMode })).join("\n");
    const result = inspectMathMarkup(html);
    assert.equal(result.formulas.length, sources.length);
    assert.deepEqual(result.issues, []);
    assert.equal(result.formulas.filter((formula) => formula.display).length, displayMode ? sources.length : 0);
  }
});

test("the reported mixed-version class failure is a hard failure", () => {
  const broken = renderMath("x_i").replaceAll("katex-sizing", "sizing");
  const codes = inspectMathMarkup(broken).issues.map((issue) => issue.code);
  assert.ok(codes.includes("legacy-renderer-class"));
  assert.ok(codes.includes("stale-renderer-output"));
});

test("non-class renderer corruption is also detected", () => {
  const broken = renderMath("x_i").replace("top:-2.55em", "top:0em");
  assert.notEqual(broken, renderMath("x_i"));
  assert.ok(inspectMathMarkup(broken).issues.some((issue) => issue.code === "stale-renderer-output"));
});

test("changing the recorded source without re-rendering is rejected", () => {
  const broken = renderMath("x_i").replace('encoding="application/x-tex">x_i', 'encoding="application/x-tex">x_j');
  assert.ok(inspectMathMarkup(broken).issues.some((issue) => issue.code === "stale-renderer-output"));
});

test("missing accessibility/source markup is rejected", () => {
  const broken = renderMath("x_i").replace("katex-mathml", "lost-mathml").replace("application/x-tex", "text/plain");
  const codes = inspectMathMarkup(broken).issues.map((issue) => issue.code);
  assert.ok(codes.includes("accessibility-markup"));
  assert.ok(codes.includes("missing-tex-source"));
});

test("parser fallbacks and unprocessed math fences are rejected", () => {
  const result = inspectMathMarkup('<span class="katex-error" title="bad TeX">broken</span><code class="language-math">x_i</code>');
  assert.deepEqual(result.issues.map((issue) => issue.code), ["parse-error", "unrendered-math"]);
});

test("ordinary text does not become a false-positive math failure", () => {
  const result = inspectMathMarkup('<p>A $10 book has <code>x_i</code> in its examples.</p>');
  assert.deepEqual(result.issues, []);
  assert.equal(result.formulas.length, 0);
});

test("raw mathematical dollars in captions cannot silently bypass the renderer", () => {
  const result = inspectMathMarkup('<figure><figcaption>For $P$, with $M=4$, the result follows.</figcaption></figure>');
  assert.equal(result.issues.filter((issue) => issue.code === "raw-math-delimiters").length, 2);
  assert.equal(findRawMathText("$P$ with $M=4$").length, 2);
  assert.equal(findRawMathText(String.raw`Display $$x_{i_j}^2 = \frac{a}{b}$$ and inline $2n-1$.`).length, 2);
});

test("raw-dollar guard preserves currency and literal code examples", () => {
  const result = inspectMathMarkup('<p>Prices are $10/$20, $10–$20, $10.00 and $20.00; $5M/year and $6M/year.</p><code>$P$</code><pre>$$x^2$$</pre><script>const tex="$M=4$";</script><style>/* $x_i$ */</style>');
  assert.deepEqual(result.issues, []);
  assert.deepEqual(findRawMathText(String.raw`Escaped \$P\$ is literal.`), []);
});

test("math selectors cannot escape the shared stylesheet", () => {
  assert.equal(inspectMathCssOwnership("article .katex .msupsub { top: 0 }", "src/styles/global.css").length, 1);
  assert.equal(inspectMathCssOwnership('<style>@media(max-width:600px){article :global(.katex-display){overflow:hidden}}</style>', "src/pages/example.astro").length, 1);
  assert.equal(inspectMathCssOwnership(".katex .msupsub { top: 0 }", "src/styles/math.css").length, 0);
});

test("CSS ownership gate ignores JavaScript, comments, declarations and Markdown code", () => {
  const astro = '<script>document.querySelector(".katex"); const example="<style>.katex{}</style>";</script><style>/* .katex{} */ .caption::before {content:".katex {example}";}</style>';
  assert.deepEqual(inspectMathCssOwnership(astro, "src/pages/example.astro"), []);
  const markdown = '```html\n<style>.katex{font-size:99em}</style>\n```\nNormal `.katex` prose.\n<style>.caption{color:gray}</style>';
  assert.deepEqual(inspectMathCssOwnership(markdown, "src/content/posts/example.md"), []);
  assert.equal(inspectMathCssOwnership('<style>.katex-sizing {font-size:99em}</style>', "src/content/posts/example.md").length, 1);
});

test("fragment refresh preserves every byte outside formula boundaries", () => {
  const prefix = '<p data-proof="A &amp; B">Unusual  spacing &copy; <a href="#step-2">link</a></p>\n<!-- keep -->';
  const suffix = '\n<section id="step-2"><p>unchanged &lt; prose</p></section>';
  const canonical = `${prefix}${renderMath("x_i")}${renderMath("a<b", { displayMode: true })}${suffix}`;
  const stale = canonical.replaceAll("katex-sizing", "sizing").replaceAll("katex-base", "base");
  assert.equal(rerenderMathHtml(stale), canonical);
});

test("fragment refresh preserves author IDs and accessibility attributes", () => {
  const original = renderMath("x_i", { displayMode: true })
    .replace('<span class="katex-display"', '<span id="eq:one" role="region" tabindex="0" aria-label="Equation one" class="katex-display author-equation"');
  const refreshed = rerenderMathHtml(original);
  assert.equal(refreshed, original);
  assert.deepEqual(inspectMathMarkup(refreshed).issues, []);
});

test("fragment refresh fails closed when the source is unavailable or invalid", () => {
  assert.throws(() => rerenderMathHtml(renderMath("x_i").replace("application/x-tex", "text/plain")), /source/i);
  assert.throws(() => rerenderMathHtml(renderMath("x_i").replace('encoding="application/x-tex">x_i', 'encoding="application/x-tex">\\notARealCommand')), /typeset/i);
});

test("the full-build gate catches missing font assets and absent math CSS", () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "angel-math-audit-"));
  try {
    fs.writeFileSync(path.join(directory, "index.html"), `<!doctype html><link rel="stylesheet" href="/math.css">${renderMath("x_i")}`);
    fs.writeFileSync(path.join(directory, "math.css"), '.katex-sizing{}.katex-base{}@font-face{font-family:KaTeX_Main;src:url("missing.woff2")}');
    let result = auditBuild(directory);
    assert.ok(result.issues.some((issue) => issue.code === "missing-css-asset"));
    fs.writeFileSync(path.join(directory, "math.css"), "body{color:black}");
    result = auditBuild(directory);
    assert.ok(result.issues.some((issue) => issue.code === "missing-math-css"));
  } finally {
    fs.rmSync(directory, { recursive: true, force: true });
  }
});
