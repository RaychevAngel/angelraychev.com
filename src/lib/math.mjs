import katex from "katex";
import { parseFragment } from "parse5";

// Rendering code, CSS and fonts must use the same pinned KaTeX release.
// Keep these options shared by components and imported manuscript fragments.
export const MATH_OPTIONS = Object.freeze({
  throwOnError: true,
  strict: "error",
  trust: false,
  output: "htmlAndMathml",
});

export function renderMath(source, { displayMode = false, label = "formula" } = {}) {
  if (typeof source !== "string" || !source.trim()) {
    throw new Error(`Missing TeX source for ${label}`);
  }
  try {
    return katex.renderToString(source, { ...MATH_OPTIONS, displayMode });
  } catch (cause) {
    throw new Error(`Unable to typeset ${label}: ${cause.message}`, { cause });
  }
}

function classes(node) {
  return new Set((node.attrs?.find(({ name }) => name === "class")?.value ?? "").split(/\s+/));
}

function annotation(node) {
  if (node.tagName === "annotation" && node.attrs?.some(({ name, value }) => name === "encoding" && value === "application/x-tex")) {
    return (node.childNodes ?? []).map((child) => child.value ?? "").join("");
  }
  for (const child of node.childNodes ?? []) {
    const source = annotation(child);
    if (source !== undefined) return source;
  }
}

function attribute(value) {
  return value.replaceAll("&", "&amp;").replaceAll('"', "&quot;").replaceAll("<", "&lt;");
}

/**
 * Imported manuscript HTML is a cache, not a separate rendering authority.
 * Re-render each complete formula from its preserved TeX annotation at build
 * time. Source-offset edits leave all non-math HTML, links and IDs untouched.
 */
export function rerenderMathHtml(html, { label = "imported manuscript" } = {}) {
  const tree = parseFragment(html, { sourceCodeLocationInfo: true });
  const replacements = [];
  function visit(node) {
    const names = classes(node);
    const displayMode = names.has("katex-display");
    if (displayMode || names.has("katex")) {
      const source = annotation(node);
      const location = node.sourceCodeLocation;
      if (source === undefined || !location?.startTag || !location?.endTag) {
        throw new Error(`Cannot recover complete TeX source in ${label}`);
      }
      let rendered = renderMath(source, { displayMode, label: `${label}, formula ${replacements.length + 1}` });
      // Preserve author-supplied IDs, accessibility attributes and classes on
      // the formula boundary without retaining stale engine layout styles.
      const extras = (node.attrs ?? []).filter(({ name }) => name !== "class" && name !== "style");
      const extraClasses = [...names].filter((name) => name && name !== "katex" && name !== "katex-display");
      if (extraClasses.length) {
        rendered = rendered.replace(/class="([^"]*)"/, (_, original) => `class="${original} ${attribute(extraClasses.join(" "))}"`);
      }
      if (extras.length) {
        const attributes = extras.map(({ name, value }) => `${name}="${attribute(value)}"`).join(" ");
        rendered = rendered.replace("<span ", `<span ${attributes} `);
      }
      replacements.push({ start: location.startOffset, end: location.endOffset, rendered });
      return;
    }
    for (const child of node.childNodes ?? []) visit(child);
  }
  visit(tree);
  replacements.sort((a, b) => a.start - b.start);
  const parts = [];
  let cursor = 0;
  for (const { start, end, rendered } of replacements) {
    if (start < cursor) throw new Error(`Overlapping formula boundaries in ${label}`);
    parts.push(html.slice(cursor, start), rendered);
    cursor = end;
  }
  parts.push(html.slice(cursor));
  return parts.join("");
}

export const renderMathFragment = rerenderMathHtml;
