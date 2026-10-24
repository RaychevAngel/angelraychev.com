import { parse } from "parse5";

export const TABLE_WRAPPER_CLASS = "tablewrap";
export const TABLE_SCROLL_ATTRIBUTE = "data-table-scroll";
export const TABLE_POLICY = Object.freeze({
  inferredHeaders: "Only a single, unspanned all-th thead row receives inferred column scope.",
  complexTables: "Existing spans, scopes, headers, IDs, alignment and content remain author-controlled.",
  headerSemantics: "Data tables require authored headers and explicit complex-header associations; missing semantics block deployment rather than inventing header text.",
  layoutTables: "role=presentation/none or data-table-layout exempts an explicitly identified layout table.",
  nestedTables: "Nested tables are preserved and reported, not automatically restructured.",
});

const propertyNames = { class: "className", tabindex: "tabIndex", "aria-label": "ariaLabel", "aria-labelledby": "ariaLabelledBy", "aria-hidden": "ariaHidden", colspan: "colSpan", rowspan: "rowSpan", "data-table-scroll": "dataTableScroll", "data-table-layout": "dataTableLayout", "data-table-enhanced": "dataTableEnhanced", "data-table-label": "dataTableLabel" };
const children = (node) => node.childNodes ?? node.children ?? [];
const tag = (node) => node.tagName;
export function tableAttribute(node, name) {
  const value = node.attrs?.find((item) => item.name === name)?.value ?? node.properties?.[propertyNames[name] ?? name];
  return Array.isArray(value) ? value.join(" ") : value == null ? undefined : String(value);
}
export function tableClasses(node) { return new Set((tableAttribute(node, "class") ?? "").split(/\s+/).filter(Boolean)); }
export function walkTableTree(node, callback, ancestors = []) {
  callback(node, ancestors);
  for (const child of children(node)) walkTableTree(child, callback, [...ancestors, node]);
  if (node.content) walkTableTree(node.content, callback, [...ancestors, node]);
}
export function tableText(node) {
  if (tableAttribute(node, "aria-hidden") === "true" || ["annotation", "script", "style"].includes(tag(node))) return "";
  if (node.nodeName === "#text" || node.type === "text") return node.value ?? "";
  return children(node).map(tableText).join(" ").replace(/\s+/g, " ").trim();
}
export function isLayoutTable(node) { return ["none", "presentation"].includes(tableAttribute(node, "role")) || tableAttribute(node, "data-table-layout") !== undefined; }
export function isTableWrapper(node) { return tableClasses(node).has(TABLE_WRAPPER_CLASS) || tableAttribute(node, TABLE_SCROLL_ATTRIBUTE) !== undefined; }

/** Scope is inferred only where the author's existing table structure is unambiguous. */
export function simpleColumnHeaders(table) {
  const head = children(table).find((node) => tag(node) === "thead");
  const rows = children(head ?? {}).filter((node) => tag(node) === "tr");
  if (rows.length !== 1) return [];
  const cells = children(rows[0]).filter((node) => ["th", "td"].includes(tag(node)));
  if (!cells.length || cells.some((node) => tag(node) !== "th" || Number(tableAttribute(node, "colspan") ?? 1) !== 1 || Number(tableAttribute(node, "rowspan") ?? 1) !== 1)) return [];
  return cells;
}

function nameFor(table, heading, idIndex) {
  const explicit = tableAttribute(table, "aria-label")?.trim();
  const labelled = (tableAttribute(table, "aria-labelledby") ?? "").split(/\s+/).filter(Boolean).map((id) => idIndex.get(id)).filter(Boolean).map(tableText).join(" ");
  const caption = children(table).find((node) => tag(node) === "caption");
  const description = explicit || labelled || (caption && tableText(caption)) || heading;
  return (description || "Data table").replace(/; scroll horizontally if needed$/, "");
}

function wrapperAttributes(table, heading, idIndex, existing) {
  const label = nameFor(table, heading, idIndex);
  // A name is authored accessibility too, even if role/tabindex were omitted.
  // Runtime enhancement must never erase a caption/heading reference or label.
  const preserve = existing && ["role", "tabindex", "aria-label", "aria-labelledby"].some((name) => tableAttribute(existing, name) !== undefined);
  return { class: TABLE_WRAPPER_CLASS, [TABLE_SCROLL_ATTRIBUTE]: "", "data-table-enhanced": preserve ? "preserve" : "auto", "data-table-label": label, tabindex: "0", role: "region", "aria-label": `${label}; scroll horizontally if needed` };
}

/** HAST plugin for Markdown. Postbuild normalization covers Astro/raw HTML too. */
export function rehypeTables() {
  return (tree) => {
    const idIndex = new Map();
    walkTableTree(tree, (node) => { const id = tableAttribute(node, "id"); if (id) idIndex.set(id, node); });
    let heading = "";
    function visit(node, ancestors = []) {
      if (/^h[1-6]$/.test(tag(node) ?? "")) heading = tableText(node);
      if (!node.children) return;
      node.children = node.children.map((child) => {
        if (tag(child) !== "table") { visit(child, [...ancestors, node]); return child; }
        const nested = [...ancestors, node].some((ancestor) => tag(ancestor) === "table");
        if (nested || isLayoutTable(child)) return child;
        for (const cell of simpleColumnHeaders(child)) {
          cell.properties ??= {};
          if (!tableAttribute(cell, "scope") && !tableAttribute(cell, "headers")) cell.properties.scope = "col";
        }
        const existing = [...ancestors, node].reverse().find(isTableWrapper);
        if (existing) {
          existing.properties ??= {};
          for (const [name, value] of Object.entries(wrapperAttributes(child, heading, idIndex, existing))) {
            if (name === "class" || (name === "aria-label" && tableAttribute(existing, "aria-labelledby"))) continue;
            if (tableAttribute(existing, name) === undefined) existing.properties[propertyNames[name] ?? name] = value;
          }
          return child;
        }
        const attributes = wrapperAttributes(child, heading, idIndex);
        return { type: "element", tagName: "div", properties: Object.fromEntries(Object.entries(attributes).map(([name, value]) => [propertyNames[name] ?? name, name === "class" ? [value] : value])), children: [child] };
      });
    }
    visit(tree);
  };
}

function escapeAttribute(value) { return String(value).replaceAll("&", "&amp;").replaceAll('"', "&quot;").replaceAll("<", "&lt;"); }
function attributeString(attributes) { return Object.entries(attributes).map(([name, value]) => `${name}="${escapeAttribute(value)}"`).join(" "); }

/** Source-offset edits preserve every existing byte except safe added attributes/wrappers. */
export function normalizeTableHtml(html, { label = "document" } = {}) {
  const tree = parse(html, { sourceCodeLocationInfo: true });
  const idIndex = new Map();
  walkTableTree(tree, (node) => { const id = tableAttribute(node, "id"); if (id) idIndex.set(id, node); });
  const insertions = new Map();
  const pendingAttributes = new Map();
  const insert = (offset, value) => insertions.set(offset, (insertions.get(offset) ?? "") + value);
  const addAttributes = (node, attributes) => {
    const location = node.sourceCodeLocation?.startTag;
    if (!location) throw new Error(`Missing table element source boundary in ${label}`);
    const pending = pendingAttributes.get(node) ?? {};
    for (const [name, value] of Object.entries(attributes)) {
      if (tableAttribute(node, name) === undefined && pending[name] === undefined) pending[name] = value;
    }
    pendingAttributes.set(node, pending);
  };
  let heading = "";
  let normalized = 0;
  walkTableTree(tree, (table, ancestors) => {
    if (/^h[1-6]$/.test(tag(table) ?? "")) heading = tableText(table);
    if (tag(table) !== "table" || isLayoutTable(table) || ancestors.some((node) => tag(node) === "table")) return;
    const location = table.sourceCodeLocation;
    if (!location?.startTag || !location?.endTag) throw new Error(`Cannot safely wrap an incomplete table in ${label}`);
    for (const cell of simpleColumnHeaders(table)) {
      if (!tableAttribute(cell, "scope") && !tableAttribute(cell, "headers")) addAttributes(cell, { scope: "col" });
    }
    const existing = [...ancestors].reverse().find(isTableWrapper);
    if (existing) {
      const attributes = wrapperAttributes(table, heading, idIndex, existing);
      delete attributes.class;
      if (tableAttribute(existing, "aria-labelledby")) delete attributes["aria-label"];
      addAttributes(existing, attributes);
    } else {
      insert(location.startOffset, `<div ${attributeString(wrapperAttributes(table, heading, idIndex))}>`);
      insert(location.endOffset, "</div>");
    }
    normalized += 1;
  });
  for (const [node, attributes] of pendingAttributes) {
    if (Object.keys(attributes).length) insert(node.sourceCodeLocation.startTag.endOffset - 1, ` ${attributeString(attributes)}`);
  }
  const parts = [];
  let cursor = 0;
  for (const [offset, value] of [...insertions].sort(([left], [right]) => left - right)) {
    parts.push(html.slice(cursor, offset), value);
    cursor = offset;
  }
  parts.push(html.slice(cursor));
  return { html: parts.join(""), tables: normalized, changed: insertions.size > 0 };
}

export default rehypeTables;
