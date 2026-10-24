import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { parse } from "parse5";
import { normalizeTableHtml, rehypeTables, tableAttribute, walkTableTree } from "../src/lib/tables.mjs";
import { auditTableDirectory, inspectTableCss, inspectTableMarkup } from "./table-audit.mjs";

const simple = '<table id="stages"><thead><tr><th align="left">Stage</th><th>Implementation</th></tr></thead><tbody><tr><td>CS224N</td><td>Policy and value learning</td></tr></tbody></table>';
function normalize(source) { return normalizeTableHtml(source).html; }
function nodes(source, tagName) { const result = []; walkTableTree(parse(source), (node) => { if (node.tagName === tagName) result.push(node); }); return result; }

test("normalization wraps a raw table once, with named keyboard fallback", () => {
  const result = normalize(`<h2>Project phases</h2>${simple}`);
  assert.match(result, /data-table-scroll=""/);
  assert.match(result, /data-table-enhanced="auto"/);
  assert.match(result, /data-table-label="Project phases"/);
  assert.match(result, /aria-label="Project phases; scroll horizontally if needed"/);
  assert.deepEqual(inspectTableMarkup(result).issues, []);
  assert.equal(normalize(result), result);
});

test("existing wrappers are enhanced rather than nested; authored labels/attributes survive", () => {
  const source = `<div class="tablewrap contributions-wrap" tabindex="0" role="region" aria-label="Authored contribution label" data-custom="yes">${simple}</div>`;
  const result = normalize(source);
  assert.equal(nodes(result, "div").length, 1);
  assert.match(result, /data-table-enhanced="preserve"/);
  assert.match(result, /aria-label="Authored contribution label"/);
  assert.match(result, /data-custom="yes"/);
  assert.equal(normalize(result), result);
});

test("raw wrappers with only an authored name retain ownership of their name", () => {
  for (const authored of ['aria-label="Original label"', 'aria-labelledby="heading"']) {
    const source = `<h2 id="heading">Original heading</h2><div class="tablewrap" ${authored}>${simple}</div>`;
    const result = normalize(source);
    assert.match(result, /data-table-enhanced="preserve"/);
    assert.ok(result.includes(authored));
    assert.equal(normalize(result), result);
    assert.deepEqual(inspectTableMarkup(result).issues, []);
  }
});

test("caption and existing aria naming are retained without changing IDs", () => {
  const source = '<h2 id="original">Nearby heading</h2><table id="data" aria-labelledby="original"><caption>Measured results</caption><thead><tr><th>Value</th></tr></thead><tbody><tr><td>42</td></tr></tbody></table>';
  const result = normalize(source);
  assert.match(result, /<caption>Measured results<\/caption>/);
  assert.match(result, /<table id="data" aria-labelledby="original">/);
  assert.match(result, /data-table-label="Nearby heading"/);
  assert.equal(nodes(result, "h2").length, 1);
  assert.deepEqual(inspectTableMarkup(result).issues, []);
});

test("scientific content, math markup, links and alignment remain byte-for-byte intact", () => {
  const body = '<tbody><tr id="r"><td style="text-align:right" align="right"><span class="katex"><math><mi>x</mi></math></span></td><td><a href="/source?q=1&amp;x=2">long.example.org/path</a></td></tr></tbody>';
  const result = normalize(`<table class="numeric">${body}</table>`);
  assert.ok(result.includes(body));
  assert.ok(result.includes('<table class="numeric">'));
});

test("only simple column headers get inferred scope; authored scopes are preserved", () => {
  const result = normalize(simple);
  assert.equal(nodes(result, "th").filter((cell) => tableAttribute(cell, "scope") === "col").length, 2);
  assert.match(result, /<th align="left" scope="col">/);
  const authored = normalize('<table><thead><tr><th scope="row">Special</th></tr></thead><tbody><tr><td>1</td></tr></tbody></table>');
  assert.match(authored, /<th scope="row">Special/);
});

test("rowspan, colspan and explicit header associations remain author-controlled", () => {
  const source = '<table><colgroup span="1"></colgroup><colgroup span="2"></colgroup><thead><tr><th id="a" rowspan="2" scope="col">Group</th><th id="b" colspan="2" scope="colgroup">Measures</th></tr><tr><th id="c" headers="b" scope="col">Count</th><th id="d" headers="b" scope="col">Rate</th></tr></thead><tbody><tr><th id="e" scope="row">One</th><td headers="c e" align="right">10</td><td headers="d e">25%</td></tr></tbody></table>';
  const result = normalize(source);
  assert.ok(result.includes(source));
  assert.deepEqual(inspectTableMarkup(result).issues, []);
});

test("dense numeric tables keep every row and column", () => {
  const header = '<thead><tr>' + Array.from({ length: 12 }, (_, i) => `<th>C${i}</th>`).join("") + '</tr></thead>';
  const body = '<tbody>' + Array.from({ length: 30 }, (_, row) => '<tr>' + Array.from({ length: 12 }, (_, col) => `<td>${row * 12 + col}</td>`).join("") + '</tr>').join("") + '</tbody>';
  const result = normalize(`<table>${header}${body}</table>`);
  assert.ok(result.includes(body));
  assert.equal(nodes(result, "td").length, 360);
  assert.deepEqual(inspectTableMarkup(result).issues, []);
});

test("intentional layout/nested tables are not silently rewritten", () => {
  const layout = '<table role="presentation"><tr><td><table><tr><td>Nested layout</td></tr></table></td></tr></table>';
  assert.equal(normalize(layout), layout);
  assert.deepEqual(inspectTableMarkup(layout).issues, []);
  const data = normalize('<table><tr><td>Historical mathematical layout</td></tr></table>');
  assert.ok(inspectTableMarkup(data).issues.some((issue) => issue.code === "headerless-table-review"));
  const complex = normalize('<table><thead><tr><th colspan="2">Unspecified group</th></tr><tr><th>A</th><th>B</th></tr></thead><tbody><tr><td>1</td><td>2</td></tr></tbody></table>');
  assert.ok(inspectTableMarkup(complex).issues.some((issue) => issue.code === "complex-header-associations-review"));
});

test("audit catches missing wrappers, duplicate wrappers and simple missing header scope", () => {
  assert.ok(inspectTableMarkup(simple).issues.some((issue) => issue.code === "missing-scroll-wrapper"));
  assert.ok(inspectTableMarkup(simple).issues.some((issue) => issue.code === "missing-column-scope"));
  const duplicate = `<div class="tablewrap"><div class="tablewrap">${simple}</div></div>`;
  assert.ok(inspectTableMarkup(duplicate).issues.some((issue) => issue.code === "duplicate-scroll-wrappers"));
});

test("audit catches broken header references, invalid scopes and unnamed/unfocusable wrappers", () => {
  const source = '<div class="tablewrap" tabindex="-1"><table><thead><tr><th id="x" scope="sideways">Name</th></tr></thead><tbody><tr><td headers="missing">Value</td></tr></tbody></table></div>';
  const codes = new Set(inspectTableMarkup(source).issues.map((issue) => issue.code));
  for (const code of ["keyboard-scroll", "unnamed-scroll-region", "scroll-region-role", "invalid-header-scope", "broken-header-reference"]) assert.ok(codes.has(code), code);
});

test("audit catches invalid tabindex, duplicate header IDs and broken table names", () => {
  const result = normalize('<table aria-labelledby="absent"><thead><tr><th id="same">A</th><th id="same">B</th></tr></thead><tbody><tr><td>1</td><td>2</td></tr></tbody></table>').replace('tabindex="0"', 'tabindex="no"');
  const codes = new Set(inspectTableMarkup(result).issues.map((issue) => issue.code));
  for (const code of ["keyboard-scroll", "duplicate-header-id", "broken-table-label"]) assert.ok(codes.has(code), code);
});

test("Markdown HAST plugin preserves existing node identity and avoids duplicate wrappers", () => {
  const cell = { type: "element", tagName: "th", properties: { align: "right" }, children: [{ type: "text", value: "Numeric" }] };
  const table = { type: "element", tagName: "table", properties: { id: "author-id" }, children: [{ type: "element", tagName: "thead", properties: {}, children: [{ type: "element", tagName: "tr", properties: {}, children: [cell] }] }] };
  const root = { type: "root", children: [table] };
  const transform = rehypeTables();
  transform(root); transform(root);
  assert.equal(root.children[0].tagName, "div");
  assert.equal(root.children[0].children[0], table);
  assert.equal(table.properties.id, "author-id");
  assert.equal(cell.properties.align, "right");
  assert.equal(cell.properties.scope, "col");
  assert.equal(root.children[0].properties.dataTableEnhanced, "auto");
});

test("HAST name-only wrappers are preserved rather than runtime-managed", () => {
  for (const naming of [{ ariaLabel: "Authored label" }, { ariaLabelledBy: "author-heading" }]) {
    const table = { type: "element", tagName: "table", properties: {}, children: [] };
    const wrapper = { type: "element", tagName: "div", properties: { className: ["tablewrap"], ...naming }, children: [table] };
    const root = { type: "root", children: [wrapper] };
    const transform = rehypeTables();
    transform(root); transform(root);
    assert.equal(wrapper.properties.dataTableEnhanced, "preserve");
    for (const [name, value] of Object.entries(naming)) assert.equal(wrapper.properties[name], value);
    assert.equal(wrapper.children[0], table);
    assert.equal(root.children[0], wrapper);
  }
});

test("raw complete documents retain scripts and bytes outside table insertions", () => {
  const prefix = '<!doctype html><html><head><script>const untouched="<table>";</script></head><body><h1>Archive</h1>';
  const suffix = '<footer id="original-footer">Original text &amp; references.</footer></body></html>';
  const result = normalize(prefix + simple + suffix);
  assert.ok(result.startsWith(prefix));
  assert.ok(result.endsWith(suffix));
  assert.deepEqual(inspectTableMarkup(result).issues, []);
});

test("incomplete table boundaries fail closed instead of reserializing scientific HTML", () => {
  assert.throws(() => normalize('<table><tr><td>Unclosed'), /incomplete table/);
});

const baseline = 'table{table-layout:auto;overflow-wrap:normal;word-break:normal}th[align="left"],td[align="left"]{text-align:left}th[align="center"],td[align="center"]{text-align:center}th[align="right"],td[align="right"]{text-align:right}';

test("CSS gate detects the actual intrinsic-width regression and missing baseline/alignment", () => {
  assert.deepEqual(inspectTableCss(baseline), []);
  for (const [before, after] of [["overflow-wrap:normal", "overflow-wrap:anywhere"], ["word-break:normal", "word-break:break-all"], ["table-layout:auto", "table-layout:fixed"]]) {
    const codes = new Set(inspectTableCss(baseline.replace(before, after)).map((issue) => issue.code));
    assert.ok(codes.has("unsafe-table-css"), after);
    assert.ok(codes.has("missing-table-css-baseline"), after);
  }
  assert.ok(inspectTableCss(baseline.replace('th[align="right"],td[align="right"]{text-align:right}', "")).some((issue) => issue.code === "missing-authored-alignment"));
  assert.ok(inspectTableMarkup(normalize(simple.replace('<table id="stages">', '<table id="stages" style="table-layout:fixed">'))).issues.some((issue) => issue.code === "unsafe-table-css"));
});

test("CSS guard ignores JS, comments and fenced examples, but checks actual style blocks", () => {
  assert.deepEqual(inspectTableCss('<script>const query="table{display:block}";</script><!-- table{display:block} -->', 'src/pages/example.astro'), []);
  assert.deepEqual(inspectTableCss('```html\n<style>table{display:block}</style>\n```', 'src/content/posts/example.md'), []);
  assert.deepEqual(inspectTableCss('/* table{display:block} */p::before{content:"table{display:block}"}', 'src/styles/other.css'), []);
  assert.ok(inspectTableCss('<style>article table { display:block }</style>', 'src/pages/example.astro').some((issue) => issue.code === "unsafe-table-css"));
});

test("actual table class/ID targets cannot evade the CSS guard, ancestor prose can", () => {
  const tableContext = { classes: new Set(["narrow", "numeric"]), ids: new Set(["measurements"]) };
  for (const selector of [".narrow", ".narrow , .unrelated", "article .narrow[data-astro-cid-test]", ".numeric:hover", "#measurements"]) {
    const issues = inspectTableCss(`${selector}{overflow-wrap:anywhere}`, 'built-styles.css', { requireBaseline: false, tableContext });
    assert.ok(issues.some((issue) => issue.code === "unsafe-table-css"), selector);
  }
  for (const selector of [".prose", ".narrow a", ".prose[data-label='.narrow']", ".other:not(.narrow)"]) {
    assert.deepEqual(inspectTableCss(`${selector}{overflow-wrap:anywhere}`, 'built-styles.css', { requireBaseline: false, tableContext }), [], selector);
  }
});

test("only the two reviewed screen-only compact card transforms are exempt", () => {
  const bests = '<style>@media screen and (max-width:480px){.bests,.bests thead{display:block}.bests td{overflow-wrap:anywhere}}</style>';
  assert.deepEqual(inspectTableCss(bests, 'src/pages/running/record/results.astro'), []);
  assert.deepEqual(inspectTableCss(bests.replace('(max-width:480px)', '(width<=480px)'), 'running/record/results/index.html'), []);
  assert.ok(inspectTableCss(bests, 'src/pages/unreviewed.astro').length > 0);
  assert.ok(inspectTableCss(bests.replace('screen and ', ''), 'src/pages/running/record/results.astro').length > 0);
  assert.ok(inspectTableCss(bests.replace('480px', '900px'), 'src/pages/running/record/results.astro').length > 0);
  const chronology = '<style>@media screen and (max-width:480px){.session-chronology table{display:block}.session-chronology td{overflow-wrap:anywhere}}</style>';
  assert.deepEqual(inspectTableCss(chronology, 'src/data/running/periods/2026.md'), []);
});

test("logical row grid accepts grouped headers, rowspans and rowspan zero", () => {
  for (const source of [
    '<table><colgroup span="2"></colgroup><thead><tr><th colspan="2" scope="colgroup">Group</th></tr><tr><th scope="col">A</th><th scope="col">B</th></tr></thead><tbody><tr><td rowspan="2">1</td><td>2</td></tr><tr><td>3</td></tr></tbody></table>',
    '<table><tbody><tr><th rowspan="0" scope="rowgroup">Group</th><td>1</td></tr><tr><td>2</td></tr><tr><td>3</td></tr></tbody></table>',
  ]) assert.deepEqual(inspectTableMarkup(normalize(source)).issues, []);
});

test("column-group scope matches real group boundaries, including child col spans", () => {
  const body = '<thead><tr><th rowspan="2" scope="col">Name</th><th colspan="3" scope="colgroup">Measures</th></tr><tr><th scope="col">A</th><th scope="col">B</th><th scope="col">C</th></tr></thead><tbody><tr><td>One</td><td>1</td><td>2</td><td>3</td></tr></tbody>';
  const groups = '<colgroup><col></colgroup><colgroup><col span="2"><col></colgroup>';
  assert.deepEqual(inspectTableMarkup(normalize(`<table>${groups}${body}</table>`)).issues, []);
  const absent = inspectTableMarkup(normalize(`<table>${body}</table>`));
  assert.ok(absent.issues.some((issue) => issue.code === "unmatched-column-group-header"));
  const wrong = inspectTableMarkup(normalize(`<table><colgroup span="2"></colgroup><colgroup span="2"></colgroup>${body}</table>`));
  assert.ok(wrong.issues.some((issue) => issue.code === "unmatched-column-group-header"));
});

test("logical row grid rejects missing, overlapping and out-of-group cells", () => {
  const short = normalize('<table><tr><th>A</th><th>B</th><th>C</th></tr><tr><td>1</td><td>2</td></tr></table>');
  assert.ok(inspectTableMarkup(short).issues.some((issue) => issue.code === "incomplete-row-grid"));
  const overlap = normalize('<table><tr><td>A</td><td rowspan="2">B</td><td>C</td></tr><tr><td colspan="2">X</td><td>Y</td></tr></table>');
  assert.ok(inspectTableMarkup(overlap).issues.some((issue) => issue.code === "overlapping-cells"));
  const outside = normalize('<table><tbody><tr><td rowspan="2">A</td></tr></tbody></table>');
  assert.ok(inspectTableMarkup(outside).issues.some((issue) => issue.code === "invalid-grid-span"));
});

test("built table pages must actually load shared CSS and progressive runtime", () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "table-gate-"));
  try {
    fs.writeFileSync(path.join(directory, 'tables.css'), baseline);
    fs.writeFileSync(path.join(directory, 'tables.js'), 'document.querySelectorAll("[data-table-scroll]"); const key="tableEnhanced";');
    const html = '<!doctype html><html><head><link rel="stylesheet" href="/tables.css"><script type="module" src="/tables.js"></script></head><body>' + normalize(simple) + '</body></html>';
    fs.writeFileSync(path.join(directory, 'index.html'), html);
    assert.deepEqual(auditTableDirectory(directory).issues, []);
    fs.writeFileSync(path.join(directory, 'tables.css'), baseline + '.narrow{overflow-wrap:anywhere}');
    fs.writeFileSync(path.join(directory, 'index.html'), html.replace('<table id="stages">', '<table id="stages" class="narrow">'));
    assert.ok(auditTableDirectory(directory).issues.some((issue) => issue.code === "unsafe-table-css"));
    fs.writeFileSync(path.join(directory, 'tables.css'), baseline);
    fs.writeFileSync(path.join(directory, 'index.html'), html.replace('<link rel="stylesheet" href="/tables.css">', '').replace('<script type="module" src="/tables.js"></script>', ''));
    const codes = new Set(auditTableDirectory(directory).issues.map((issue) => issue.code));
    assert.ok(codes.has("missing-table-css-baseline"));
    assert.ok(codes.has("missing-table-runtime"));
  } finally { fs.rmSync(directory, { recursive: true, force: true }); }
});
