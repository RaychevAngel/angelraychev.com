#!/usr/bin/env node
/** Build-time structure/accessibility gate; browser geometry is checked separately. */
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { parse } from "parse5";
import { TABLE_POLICY, isLayoutTable, isTableWrapper, simpleColumnHeaders, tableAttribute as attr, tableText, walkTableTree } from "../src/lib/tables.mjs";

const projectRoot = fileURLToPath(new URL("../", import.meta.url));
const ownedTableStyle = "src/styles/tables.css";

/** Small declaration parser; strings/comments and JS are never scanned as CSS. */
function cssRules(css) {
  const rules = [];
  const stack = [];
  let buffer = "", quote = null, comment = false;
  const declaration = () => {
    const colon = buffer.indexOf(":");
    const current = stack.at(-1);
    if (colon > 0 && current && !current.prelude.startsWith("@")) current.declarations.push({ property: buffer.slice(0, colon).trim().toLowerCase(), value: buffer.slice(colon + 1).trim().toLowerCase() });
    buffer = "";
  };
  for (let index = 0; index < css.length; index += 1) {
    const char = css[index];
    if (comment) { if (char === "*" && css[index + 1] === "/") { comment = false; index += 1; } continue; }
    if (quote) { buffer += char; if (char === "\\" && index + 1 < css.length) buffer += css[++index]; else if (char === quote) quote = null; continue; }
    if (char === "/" && css[index + 1] === "*") { comment = true; index += 1; continue; }
    if (char === '"' || char === "'") { quote = char; buffer += char; continue; }
    if (char === "{") {
      const rule = { prelude: buffer.trim(), contexts: stack.map((parent) => parent.prelude).filter((prelude) => prelude.startsWith("@")), declarations: [] };
      stack.push(rule); buffer = "";
    } else if (char === ";") declaration();
    else if (char === "}") { declaration(); const rule = stack.pop(); if (rule && !rule.prelude.startsWith("@")) rules.push(rule); }
    else buffer += char;
  }
  return rules;
}

function styleBlocks(source, filename) {
  if (filename.endsWith(".css")) return [source];
  let input = source;
  if (filename.endsWith(".md")) {
    let fence = null;
    input = input.split("\n").map((line) => {
      const match = line.match(/^\s{0,3}(`{3,}|~{3,})/);
      if (!fence && match) { fence = match[1]; return ""; }
      if (fence) { if (match && match[1][0] === fence[0] && match[1].length >= fence.length) fence = null; return ""; }
      return line;
    }).join("\n");
  }
  input = input.replace(/^---[\s\S]*?\n---/, "").replace(/<script\b[^>]*>[\s\S]*?<\/script\s*>/gi, "");
  return [...input.matchAll(/<style\b[^>]*>([\s\S]*?)<\/style\s*>/gi)].map((match) => match[1]);
}

function approvedMobileCard(selector, contexts, filename) {
  const compactMedia = contexts.some((context) => /@media\s+screen\b/i.test(context) && /\(\s*(?:max-width\s*:\s*480px|width\s*<=\s*480px)\s*\)/i.test(context));
  if (!compactMedia) return false;
  if (filename === "src/pages/running/record/results.astro" || filename === "running/record/results/index.html") return selector.trim().startsWith(".bests");
  if (filename === "src/data/running/periods/2026.md" || filename === "running/record/2026/index.html") return selector.trim().startsWith(".session-chronology");
  // Combined built styles contain these two reviewed, narrowly scoped rules.
  if (filename === "built-styles.css") return /^\s*\.(?:bests|session-chronology)(?:\b|\[)/.test(selector);
  return false;
}

/** Class-only rules are relevant only when their target is a real table element. */
function contextualTableSelector(selector, context) {
  if (!context) return false;
  selector = selector.trim();
  let start = 0, brackets = 0, parentheses = 0, quote = null;
  for (let index = 0; index < selector.length; index += 1) {
    const char = selector[index];
    if (quote) { if (char === "\\") index += 1; else if (char === quote) quote = null; continue; }
    if (char === '"' || char === "'") { quote = char; continue; }
    if (char === "[") brackets += 1;
    else if (char === "]") brackets -= 1;
    else if (!brackets && char === "(") parentheses += 1;
    else if (!brackets && char === ")") parentheses -= 1;
    else if (!brackets && !parentheses && /[\s>+~]/.test(char)) start = index + 1;
  }
  // Scoped attributes and pseudo-function arguments are qualifiers, not direct
  // element class/ID tokens. This intentionally handles ordinary compound
  // selectors rather than claiming to implement all of Selectors Level 4.
  const compound = selector.slice(start).replace(/\[[^\]]*\]/g, "").replace(/:[\w-]+\([^)]*\)/g, "");
  for (const match of compound.matchAll(/([.#])([A-Za-z_][\w-]*)/g)) {
    if (match[1] === "." && context.classes?.has(match[2])) return true;
    if (match[1] === "#" && context.ids?.has(match[2])) return true;
  }
  return false;
}

function tableSelector(selector, context) {
  return /(?:^|[\s>+~,(])(?:table|thead|tbody|tfoot|tr|th|td)(?=[\s.#:[>+~,)\]]|$)/.test(selector) || /^\s*\.(?:bests|session-chronology)(?:\b|\[)/.test(selector) || contextualTableSelector(selector, context);
}

export function inspectTableCss(source, filename = ownedTableStyle, { requireBaseline = filename === ownedTableStyle, tableContext = null } = {}) {
  const normalized = filename.split(path.sep).join("/").replace(/^\.\//, "");
  const rules = styleBlocks(source, normalized).flatMap(cssRules);
  const issues = [];
  for (const rule of rules) for (const selector of rule.prelude.split(",")) {
    if (!tableSelector(selector, tableContext)) continue;
    for (const { property, value } of rule.declarations) {
      const plain = value.replace(/\s*!important\s*$/, "").trim();
      const dangerous = (property === "overflow-wrap" && plain === "anywhere") || (property === "word-break" && ["break-all", "break-word"].includes(plain)) || (property === "table-layout" && plain === "fixed") || (property === "display" && ["block", "inline-block", "grid", "flex", "inline-flex", "inline-grid"].includes(plain));
      if (dangerous && !approvedMobileCard(selector, rule.contexts, normalized)) issues.push({ code: "unsafe-table-css", document: normalized, message: `Unreviewed ${property}:${value} on ${selector.trim()}.` });
    }
  }
  if (requireBaseline) {
    const tableRules = rules.filter((rule) => rule.prelude.split(",").some((selector) => selector.trim() === "table") && !rule.contexts.length);
    for (const [property, value] of [["overflow-wrap", "normal"], ["word-break", "normal"], ["table-layout", "auto"]]) {
      if (!tableRules.some((rule) => rule.declarations.some((declaration) => declaration.property === property && declaration.value === value))) issues.push({ code: "missing-table-css-baseline", document: normalized, message: `Shared table styles must explicitly set ${property}:${value}.` });
    }
    for (const alignment of ["left", "center", "right"]) for (const cell of ["th", "td"]) {
      const selector = new RegExp(`${cell}\\[align\\s*=\\s*["']?${alignment}["']?\\]`);
      if (!rules.some((rule) => selector.test(rule.prelude) && rule.declarations.some(({ property, value }) => property === "text-align" && value === alignment))) issues.push({ code: "missing-authored-alignment", document: normalized, message: `Preserve ${cell}[align="${alignment}"] with text-align:${alignment}.` });
    }
  }
  return issues;
}

function ownRows(table) {
  const groups = [];
  for (const child of table.childNodes ?? []) {
    if (["thead", "tbody", "tfoot"].includes(child.tagName)) groups.push((child.childNodes ?? []).filter((row) => row.tagName === "tr"));
    else if (child.tagName === "tr") groups.push([child]);
  }
  return groups;
}

export function inspectTableGrid(table) {
  const issues = [], warnings = [], rows = [], placements = [];
  const dynamic = (attr(table, "class") ?? "").split(/\s+/).includes("capabilities");
  for (const group of ownRows(table)) {
    const occupied = Array.from({ length: group.length }, () => []);
    for (let rowIndex = 0; rowIndex < group.length; rowIndex += 1) {
      const row = group[rowIndex];
      const cells = (row.childNodes ?? []).filter((cell) => ["th", "td"].includes(cell.tagName));
      if (!cells.length && dynamic && attr(row, "id") === "arm-capabilities") { warnings.push({ code: "client-populated-row", message: "Known capabilities row is populated by the explorer; author structure retained." }); continue; }
      let column = 0;
      for (const cell of cells) {
        while (occupied[rowIndex][column]) column += 1;
        const columns = Number(attr(cell, "colspan") ?? 1);
        const requestedRows = Number(attr(cell, "rowspan") ?? 1);
        const spanRows = requestedRows === 0 ? group.length - rowIndex : requestedRows;
        if (!Number.isInteger(columns) || columns < 1 || columns > 1000 || !Number.isInteger(spanRows) || spanRows < 1 || spanRows > group.length - rowIndex) { issues.push({ code: "invalid-grid-span", message: "A cell span is invalid or extends beyond its row group." }); continue; }
        placements.push({ cell, column, columns });
        for (let down = 0; down < spanRows; down += 1) for (let across = 0; across < columns; across += 1) {
          const target = occupied[rowIndex + down];
          if (target[column + across]) issues.push({ code: "overlapping-cells", message: "A cell span overlaps an earlier rowspan." });
          target[column + across] = true;
        }
        column += columns;
      }
      rows.push(occupied[rowIndex]);
    }
  }
  const width = Math.max(0, ...rows.map((row) => row.length));
  for (const [row, slots] of rows.entries()) if (slots.length !== width || Array.from({ length: width }, (_, column) => slots[column]).some((slot) => !slot)) issues.push({ code: "incomplete-row-grid", message: `Row ${row + 1} does not cover all ${width} logical columns.` });
  const columnGroups = [];
  let column = 0;
  for (const group of (table.childNodes ?? []).filter((node) => node.tagName === "colgroup")) {
    const columns = (group.childNodes ?? []).filter((node) => node.tagName === "col");
    const widths = columns.length ? columns.map((node) => Number(attr(node, "span") ?? 1)) : [Number(attr(group, "span") ?? 1)];
    if (widths.some((span) => !Number.isInteger(span) || span < 1 || span > 1000)) { issues.push({ code: "invalid-column-group", message: "A colgroup/col span must be a positive bounded integer." }); continue; }
    const span = widths.reduce((sum, value) => sum + value, 0);
    columnGroups.push({ start: column, end: column + span });
    column += span;
  }
  for (const placement of placements.filter(({ cell }) => cell.tagName === "th" && attr(cell, "scope") === "colgroup")) {
    if (!columnGroups.some((group) => group.start === placement.column && group.end === placement.column + placement.columns)) issues.push({ code: "unmatched-column-group-header", message: `A scope=colgroup header covering columns ${placement.column + 1}–${placement.column + placement.columns} needs a corresponding colgroup with the same boundaries.` });
  }
  return { columns: width, rows: rows.length, issues, warnings };
}

export function inspectTableMarkup(html, label = "document") {
  const root = parse(html);
  const ids = new Map();
  walkTableTree(root, (node) => { const id = attr(node, "id"); if (id) ids.set(id, node); });
  const issues = [];
  const warnings = [];
  const tables = [];
  const add = (collection, code, index, message) => collection.push({ code, document: label, table: index, message });
  walkTableTree(root, (table, ancestors) => {
    if (table.tagName !== "table") return;
    const index = tables.length;
    const nested = ancestors.some((node) => node.tagName === "table");
    const layout = isLayoutTable(table);
    const wrappers = ancestors.filter(isTableWrapper);
    const cells = [];
    walkTableTree(table, (node, cellAncestors) => {
      if (["th", "td"].includes(node.tagName) && !cellAncestors.some((parent) => parent !== table && parent.tagName === "table")) cells.push(node);
    });
    const headerCells = cells.filter((node) => node.tagName === "th");
    tables.push({ index, layout, nested, cells: cells.length, headers: headerCells.length, wrapperCount: wrappers.length, caption: tableText((table.childNodes ?? []).find((node) => node.tagName === "caption") ?? {}), id: attr(table, "id") ?? null });
    if (layout) return;
    if (nested) { add(warnings, "nested-table-review", index, "Nested table retained under the explicit non-restructuring policy."); return; }
    const grid = inspectTableGrid(table);
    for (const finding of grid.issues) add(issues, finding.code, index, finding.message);
    for (const finding of grid.warnings) add(warnings, finding.code, index, finding.message);
    if (wrappers.length !== 1) add(issues, wrappers.length ? "duplicate-scroll-wrappers" : "missing-scroll-wrapper", index, `Expected one owned scroll wrapper, found ${wrappers.length}.`);
    const wrapper = wrappers.at(-1);
    if (wrapper) {
      if (!/^\+?\d+$/.test(attr(wrapper, "tabindex") ?? "")) add(issues, "keyboard-scroll", index, "Scroll wrapper needs a nonnegative integer tabindex.");
      if (attr(wrapper, "role") !== "region") add(issues, "scroll-region-role", index, "Scroll wrapper needs role=region.");
      if (attr(wrapper, "data-table-scroll") === undefined || !["auto", "preserve"].includes(attr(wrapper, "data-table-enhanced")) || !attr(wrapper, "data-table-label")?.trim()) add(issues, "missing-progressive-contract", index, "Expected scroll marker, ownership mode and base label for progressive enhancement.");
      const references = (attr(wrapper, "aria-labelledby") ?? "").split(/\s+/).filter(Boolean);
      const named = attr(wrapper, "aria-label")?.trim() || (references.length && references.every((id) => ids.has(id) && tableText(ids.get(id)).trim()));
      if (!named) add(issues, "unnamed-scroll-region", index, "Scroll wrapper needs an accurate accessible name.");
    }
    for (const header of simpleColumnHeaders(table)) {
      if (!attr(header, "scope") && !attr(header, "headers")) add(issues, "missing-column-scope", index, "Simple thead column headers need scope=col or explicit header associations.");
    }
    if (!headerCells.length) add(issues, "headerless-table-review", index, "Data table has no authored headers. Review its semantics: add the correct th headers or explicitly identify a genuine layout table; no heading text is invented.");
    const tableHeaders = new Map(headerCells.filter((cell) => attr(cell, "id")).map((cell) => [attr(cell, "id"), cell]));
    for (const header of headerCells) {
      const id = attr(header, "id");
      if (id && headerCells.filter((cell) => attr(cell, "id") === id).length > 1) add(issues, "duplicate-header-id", index, `Header ID ${id} is repeated within this table.`);
    }
    for (const id of (attr(table, "aria-labelledby") ?? "").split(/\s+/).filter(Boolean)) {
      if (!ids.has(id) || !tableText(ids.get(id)).trim()) add(issues, "broken-table-label", index, `Table aria-labelledby=${id} does not identify usable naming text.`);
    }
    if (!simpleColumnHeaders(table).length && headerCells.some((cell) => !attr(cell, "scope") && !attr(cell, "headers"))) add(issues, "complex-header-associations-review", index, "Complex header cells need authored scope/headers associations before deployment; review the semantics rather than inferring scientific structure.");
    for (const cell of cells) {
      const scope = attr(cell, "scope");
      if (scope && !["row", "col", "rowgroup", "colgroup", "auto"].includes(scope)) add(issues, "invalid-header-scope", index, `Invalid scope=${scope}.`);
      if (scope && cell.tagName !== "th") add(issues, "scope-on-data-cell", index, "scope belongs on header cells, not td.");
      for (const id of (attr(cell, "headers") ?? "").split(/\s+/).filter(Boolean)) {
        if (!tableHeaders.has(id)) add(issues, "broken-header-reference", index, `headers=${id} does not identify a th in this table.`);
      }
      for (const name of ["colspan", "rowspan"]) {
        const value = attr(cell, name);
        if (value !== undefined && (!/^\d+$/.test(value) || Number(value) < (name === "rowspan" ? 0 : 1))) add(issues, "invalid-cell-span", index, `Invalid ${name}=${value}.`);
      }
    }
    for (const element of [table, ...cells]) {
      const inline = attr(element, "style");
      if (inline) for (const issue of inspectTableCss(`${element.tagName}{${inline}}`, "inline.css", { requireBaseline: false })) add(issues, issue.code, index, issue.message);
    }
  });
  return { document: label, tables, issues, warnings, policy: TABLE_POLICY };
}

export function auditTableDirectory(directory) {
  function files(folder) { return fs.readdirSync(folder, { withFileTypes: true }).flatMap((entry) => entry.isDirectory() ? files(path.join(folder, entry.name)) : entry.name.endsWith(".html") ? [path.join(folder, entry.name)] : []); }
  const htmlFiles = files(directory);
  const documents = htmlFiles.map((filename) => {
    const html = fs.readFileSync(filename, "utf8");
    const relative = path.relative(directory, filename);
    const report = inspectTableMarkup(html, relative);
    if (report.tables.some((table) => !table.layout && !table.nested)) {
      const tree = parse(html), styles = [], modules = [];
      const tableContext = { classes: new Set(), ids: new Set() };
      const asset = (url) => { if (!url || /^(?:[a-z]+:)?\/\//i.test(url)) return ""; const filename = path.resolve(directory, `.${url.startsWith("/") ? url.split(/[?#]/)[0] : `/${path.dirname(relative)}/${url.split(/[?#]/)[0]}`}`); return filename.startsWith(path.resolve(directory) + path.sep) && fs.existsSync(filename) ? fs.readFileSync(filename, "utf8") : ""; };
      walkTableTree(tree, (node) => {
        if (["table", "thead", "tbody", "tfoot", "tr", "th", "td", "col", "colgroup", "caption"].includes(node.tagName)) {
          for (const name of (attr(node, "class") ?? "").split(/\s+/).filter(Boolean)) tableContext.classes.add(name);
          const id = attr(node, "id"); if (id) tableContext.ids.add(id);
        }
        if (node.tagName === "link" && (attr(node, "rel") ?? "").split(/\s+/).includes("stylesheet")) styles.push(asset(attr(node, "href")));
        if (node.tagName === "style") styles.push((node.childNodes ?? []).map((child) => child.value ?? "").join(""));
        if (node.tagName === "script" && attr(node, "type") === "module") modules.push(attr(node, "src") ? asset(attr(node, "src")) : (node.childNodes ?? []).map((child) => child.value ?? "").join(""));
      });
      const css = styles.join("\n");
      // Asset presence is independently checked for every table-containing page.
      const baseline = inspectTableCss(css, "built-styles.css", { requireBaseline: true, tableContext });
      if (baseline.length) report.issues.push(...baseline.map((issue) => ({ ...issue, document: relative })));
      const inline = inspectTableCss(html, relative, { requireBaseline: false, tableContext });
      report.issues.push(...inline);
      const runtime = modules.join("\n");
      if (!runtime.includes("data-table-scroll") || !runtime.includes("tableEnhanced")) report.issues.push({ code: "missing-table-runtime", document: relative, message: "Expected the shared progressive table-layout module in built table pages." });
    }
    return report;
  });
  // Include every CSS-owning source format, not only emitted HTML.
  function sourceFiles(folder) { return fs.readdirSync(folder, { withFileTypes: true }).flatMap((entry) => entry.isDirectory() ? sourceFiles(path.join(folder, entry.name)) : /\.(?:css|astro|md|html)$/.test(entry.name) ? [path.join(folder, entry.name)] : []); }
  const cssIssues = sourceFiles(path.join(projectRoot, "src")).flatMap((filename) => inspectTableCss(fs.readFileSync(filename, "utf8"), path.relative(projectRoot, filename)));
  return { htmlFiles: htmlFiles.length, tablePages: documents.filter((document) => document.tables.length).length, tables: documents.reduce((count, document) => count + document.tables.length, 0), issues: [...documents.flatMap((document) => document.issues), ...cssIssues], warnings: documents.flatMap((document) => document.warnings), documents: documents.filter((document) => document.tables.length), policy: TABLE_POLICY };
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const result = auditTableDirectory(path.resolve(process.argv[2] ?? "dist"));
  console.log(JSON.stringify({ ...result, documents: undefined }, null, 2));
  if (result.issues.length) process.exitCode = 1;
}
