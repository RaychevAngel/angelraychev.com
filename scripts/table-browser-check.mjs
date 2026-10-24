/** Read-only DOM probe for approved CUA evaluate; no browser driver or DOM changes. */
import path from "node:path";
import { fileURLToPath } from "node:url";

export async function inspectTableLayout({ compact = true, tableLimit = 8, issueLimit = 30 } = {}) {
  try { if (document.fonts?.ready) await document.fonts.ready; } catch { /* Restricted browser bridges may omit FontFaceSet. */ }
  const issues = [];
  const skipped = [];
  let rangeChecksAvailable = typeof document.createRange === "function";
  const rectangle = (node) => { const r = node.getBoundingClientRect(); return { x: r.x, y: r.y, width: r.width, height: r.height, right: r.right, bottom: r.bottom }; };
  const records = [...document.querySelectorAll("table")].map((table, index) => {
    const add = (code, message, extra = {}) => issues.push({ table: index, code, message, ...extra });
    const layout = ["presentation", "none"].includes(table.getAttribute("role")) || table.hasAttribute("data-table-layout");
    const nested = Boolean(table.parentElement?.closest("table"));
    const box = rectangle(table);
    const visible = box.width > 0 && box.height > 0 && getComputedStyle(table).visibility !== "hidden";
    if (layout || nested || !visible) { skipped.push({ table: index, reason: layout ? "explicit-layout" : nested ? "nested-author-controlled" : "not-currently-visible" }); return { index, layout, nested, visible }; }
    const wrappers = [];
    for (let node = table.parentElement; node; node = node.parentElement) if (node.classList.contains("tablewrap") || node.hasAttribute("data-table-scroll")) wrappers.push(node);
    if (wrappers.length !== 1) add("scroll-wrapper-count", `Expected one scroll wrapper, found ${wrappers.length}.`);
    const wrapper = wrappers[0];
    const overflow = Boolean(wrapper && wrapper.scrollWidth > wrapper.clientWidth + 1);
    if (wrapper) {
      const style = getComputedStyle(wrapper);
      if (overflow && !["auto", "scroll"].includes(style.overflowX)) add("unscrollable-table", "Wide table is not in a horizontally scrollable container.");
      const references = (wrapper.getAttribute("aria-labelledby") ?? "").split(/\s+/).filter(Boolean);
      const named = wrapper.getAttribute("aria-label")?.trim() || (references.length && references.every((id) => document.getElementById(id)?.textContent?.trim()));
      if (overflow && (wrapper.tabIndex < 0 || !named || wrapper.getAttribute("role") !== "region")) add("inaccessible-scroll", "Overflow needs a keyboard-focusable named region.");
      if (style.overflowY === "hidden" || style.overflowY === "clip") {
        const w = rectangle(wrapper);
        if (box.y < w.y - 1 || box.bottom > w.bottom + 1) add("vertical-clipping", "The scroll container clips table rows.");
      }
    }
    const cells = [...table.querySelectorAll("th,td")].filter((cell) => cell.closest("table") === table);
    for (const cell of cells) {
      const c = rectangle(cell);
      if (!c.width || !c.height || getComputedStyle(cell).display === "none") continue;
      if (cell.scrollWidth > cell.clientWidth + 2 && ["hidden", "clip"].includes(getComputedStyle(cell).overflowX)) add("cell-content-clipped", "A cell clips overflowing content.", { text: cell.textContent?.trim().slice(0, 100) });
    }
    // Geometry, not a blanket CSS ban: custom responsive cards may intentionally
    // use overflow-wrap:anywhere while still keeping ordinary words intact.
    const probes = [...table.querySelectorAll("th"), ...[...table.querySelectorAll("tbody tr")].slice(0, 6).map((row) => row.querySelector("td,th"))].filter(Boolean);
    let wordChecks = 0;
    if (rangeChecksAvailable) for (const cell of probes) {
      const c = rectangle(cell);
      if (!c.width || !c.height || getComputedStyle(cell).display === "none") continue;
      function textNodes(node) { return node.nodeType === 3 ? [node] : [...node.childNodes].flatMap(textNodes); }
      for (const node of textNodes(cell)) {
        if (node.parentElement?.closest("a,code,.katex,[data-table-break=anywhere]")) continue;
        const words = [...(node.textContent ?? "").matchAll(/[\p{L}\p{N}]{3,32}/gu)].slice(0, 6);
        for (const word of words) {
          try {
            const range = document.createRange();
            range.setStart(node, word.index);
            range.setEnd(node, word.index + word[0].length);
            const lines = new Set([...range.getClientRects()].filter((r) => r.width > 0 && r.height > 0).map((r) => Math.round(r.top * 2) / 2));
            wordChecks += 1;
            if (lines.size > 1) add("ordinary-word-split", "An ordinary short word is broken across lines inside a cell.", { word: word[0], cellWidth: c.width });
            range.detach?.();
          } catch { rangeChecksAvailable = false; break; }
        }
        if (!rangeChecksAvailable) break;
      }
      if (!rangeChecksAvailable) break;
    }
    return { index, visible, box, columns: table.rows?.[0]?.cells?.length ?? null, wrapperWidth: wrapper?.clientWidth ?? null, scrollWidth: wrapper?.scrollWidth ?? null, overflow, wordChecks };
  });
  const width = document.documentElement.clientWidth;
  if (document.documentElement.scrollWidth > width + 1) issues.push({ code: "page-horizontal-overflow", width, scrollWidth: document.documentElement.scrollWidth });
  return { url: location.href, theme: document.documentElement.dataset.theme, viewport: { width: innerWidth, height: innerHeight }, tables: records.length, rangeChecksAvailable, records: compact ? records.slice(0, tableLimit) : records, skipped, issues: compact ? issues.slice(0, issueLimit) : issues, issueCount: issues.length, qualification: "Mechanical structure and layout checks do not replace screenshot review, keyboard exercise, print review or content judgment." };
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url) && process.argv.includes("--print")) console.log(`(${inspectTableLayout.toString()})()`);
