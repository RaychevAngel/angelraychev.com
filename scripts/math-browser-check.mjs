/**
 * Read-only browser probe. Run through the approved CUA browser evaluate API,
 * not a separate browser automation driver. `node ... --print` emits the expression.
 */
import path from "node:path";
import { fileURLToPath } from "node:url";

export async function inspectMathLayout({ compact = true, formulaLimit = 8, issueLimit = 30 } = {}) {
  let fontApi = null;
  try {
    fontApi = document.fonts ?? null;
    if (fontApi?.ready) await fontApi.ready;
  } catch { /* Some restricted browser bridges do not expose FontFaceSet. */ }
  const fontCheckAvailable = typeof fontApi?.check === "function";
  const rect = (element) => {
    const box = element.getBoundingClientRect();
    return { x: box.x, y: box.y, width: box.width, height: box.height, right: box.right, bottom: box.bottom };
  };
  const issues = [];
  const formulas = [...document.querySelectorAll(".katex")].map((element, index) => {
    const visual = element.querySelector(".katex-html");
    const source = element.querySelector('annotation[encoding="application/x-tex"]')?.textContent ?? null;
    const box = rect(element);
    if (!visual || !source || !element.querySelector(".katex-mathml math")) issues.push({ index, code: "missing-output-or-source", source });
    if (!box.width || !box.height) issues.push({ index, code: "zero-size-formula", source });
    const legacy = element.querySelector(".base, .strut, .sizing");
    if (legacy) issues.push({ index, code: "legacy-renderer-markup", source });
    const display = element.closest(".katex-display");
    const displayBox = display ? rect(display) : null;
    const visualBox = visual ? rect(visual) : null;
    if (display && visualBox && displayBox) {
      const style = getComputedStyle(display);
      if (style.overflowY === "hidden" || style.overflowY === "clip") {
        if (visualBox.y < displayBox.y - 1 || visualBox.bottom > displayBox.bottom + 1) issues.push({ index, code: "display-vertical-clipping", source });
      }
      if (display.scrollWidth > display.clientWidth + 1 && (display.tabIndex < 0 || !display.getAttribute("aria-label"))) {
        issues.push({ index, code: "inaccessible-equation-scroll", source });
      }
    }
    if (!display && element.classList.contains("math-inline-overflow")) {
      if (element.scrollWidth > element.clientWidth + 1 && (element.tabIndex < 0 || !element.getAttribute("aria-label"))) {
        issues.push({ index, code: "inaccessible-inline-equation-scroll", source });
      }
    }
    return { index, source, display: Boolean(display), box, visualBox, displayBox };
  });
  for (const error of document.querySelectorAll(".katex-error")) issues.push({ code: "parse-error", message: error.getAttribute("title") ?? error.textContent });
  const probes = [];
  for (const kind of ["subscript", "superscript"]) {
    for (const wrapper of document.querySelectorAll(`[data-math-probe="${kind}"]`)) {
      const visual = wrapper.querySelector(".katex-html");
      const base = visual?.querySelector(".mord > .mathnormal");
      const script = visual?.querySelector(".msupsub .katex-sizing");
      if (!base || !script) { issues.push({ code: "missing-geometry-probe", kind }); continue; }
      const baseBox = rect(base);
      const scriptBox = rect(script);
      const baseFont = Number.parseFloat(getComputedStyle(base).fontSize);
      const scriptFont = Number.parseFloat(getComputedStyle(script).fontSize);
      const delta = scriptBox.y + scriptBox.height / 2 - (baseBox.y + baseBox.height / 2);
      const okay = scriptFont < baseFont * 0.9 && (kind === "subscript" ? delta > 1 : delta < -1);
      probes.push({ kind, baseFont, scriptFont, centerDisplacement: delta, okay });
      if (!okay) issues.push({ code: "script-position-or-size", kind, baseFont, scriptFont, centerDisplacement: delta });
    }
  }
  const documentWidth = document.documentElement.clientWidth;
  if (document.documentElement.scrollWidth > documentWidth + 1) issues.push({ code: "page-horizontal-overflow", width: documentWidth, scrollWidth: document.documentElement.scrollWidth });
  const usedFonts = new Set();
  for (const node of document.querySelectorAll(".katex-html span")) {
    if (node.children.length || !node.textContent?.trim()) continue;
    const style = getComputedStyle(node);
    const family = style.fontFamily.split(",")[0].trim().replace(/^['"]|['"]$/g, "");
    if (!family.startsWith("KaTeX_")) continue;
    const spec = `${style.fontStyle} ${style.fontWeight} ${style.fontSize} "${family}"`;
    usedFonts.add(spec);
    if (fontCheckAvailable && !fontApi.check(spec)) issues.push({ code: "math-font-not-ready", font: spec });
  }
  return { url: location.href, theme: document.documentElement.dataset.theme,
    viewport: { width: innerWidth, height: innerHeight }, equations: formulas.length,
    fontCheckAvailable, fontStatus: fontApi?.status ?? "unavailable", usedFonts: [...usedFonts], probes,
    formulas: compact ? formulas.slice(0, formulaLimit) : formulas,
    issues: compact ? issues.slice(0, issueLimit) : issues, issueCount: issues.length,
    qualification: "Mechanical/browser-layout checks, not a proof of visual or mathematical correctness. Review screenshots too." };
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url) && process.argv.includes("--print")) {
  console.log(`(${inspectMathLayout.toString()})()`);
}
