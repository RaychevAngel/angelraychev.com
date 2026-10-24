#!/usr/bin/env node
/** Mechanical deployment gate. Browser typography review remains a separate gate. */
import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import { createHash } from "node:crypto";
import { parse, parseFragment } from "parse5";
import { renderMath } from "../src/lib/math.mjs";

const projectRoot = fileURLToPath(new URL("../", import.meta.url));
const localRequire = createRequire(new URL("../package.json", import.meta.url));
const legacyClasses = new Set(["base", "strut", "sizing"]);
const ownedMathStyle = "src/styles/math.css";
const mathSelector = /\.(?:katex(?:-[\w-]+)?|math-inline-overflow|msupsub|vlist(?:-[\w-]+)?|mathnormal|mord|mbin|mrel|mopen|mclose|mpunct|minner|mspace|mtight|pstrut)\b|\[\s*class\s*[~|^$*]?=\s*["'][^"']*\bkatex\b/;

function filesBelow(directory, suffix) {
  if (!fs.existsSync(directory)) return [];
  return fs.readdirSync(directory, { withFileTypes: true }).flatMap((item) => {
    const target = path.join(directory, item.name);
    return item.isDirectory() ? filesBelow(target, suffix) : target.endsWith(suffix) ? [target] : [];
  });
}

function walk(node, callback) {
  callback(node);
  for (const child of node.childNodes ?? []) walk(child, callback);
  if (node.content) walk(node.content, callback);
}

function nodesWhere(node, predicate) {
  const matches = [];
  walk(node, (candidate) => { if (predicate(candidate)) matches.push(candidate); });
  return matches;
}

function attr(node, name) {
  return node.attrs?.find((item) => item.name === name)?.value;
}

function classes(node) {
  return new Set((attr(node, "class") ?? "").split(/\s+/).filter(Boolean));
}

function text(node) {
  return node.nodeName === "#text" ? node.value : (node.childNodes ?? []).map(text).join("");
}

function canonical(node, root = false) {
  if (node.nodeName === "#text") return ["text", node.value];
  // Author IDs/ARIA/classes on the boundary are not engine layout internals.
  const attributes = root ? [["class", "katex"]] : (node.attrs ?? []).map(({ name, value }) => [name, value]).sort();
  return [node.nodeName, attributes,
    (node.childNodes ?? []).map((child) => canonical(child))];
}

function stripMarkdownCode(source) {
  let fence = null;
  return source.split("\n").map((line) => {
    const match = line.match(/^\s{0,3}(`{3,}|~{3,})/);
    if (!fence && match) { fence = match[1]; return ""; }
    if (fence) {
      if (match && match[1][0] === fence[0] && match[1].length >= fence.length) fence = null;
      return "";
    }
    return line.replace(/(`+)[\s\S]*?\1/g, "");
  }).join("\n");
}

/** Read rule preludes only: declaration strings and JavaScript queries are not CSS selectors. */
function selectorsInCss(css) {
  const selectors = [];
  let buffer = "";
  let quote = null;
  let comment = false;
  for (let index = 0; index < css.length; index += 1) {
    const char = css[index];
    if (comment) {
      if (char === "*" && css[index + 1] === "/") { comment = false; index += 1; }
      continue;
    }
    if (quote) {
      buffer += char;
      if (char === "\\" && index + 1 < css.length) buffer += css[++index];
      else if (char === quote) quote = null;
      continue;
    }
    if (char === "/" && css[index + 1] === "*") { comment = true; index += 1; continue; }
    if (char === '"' || char === "'") { quote = char; buffer += char; continue; }
    if (char === "{") {
      const prelude = buffer.trim();
      if (prelude && !prelude.startsWith("@")) selectors.push(prelude);
      buffer = "";
    } else if (char === ";" || char === "}") buffer = "";
    else buffer += char;
  }
  return selectors;
}

export function inspectMathCssOwnership(source, filename) {
  const normalized = filename.split(path.sep).join("/").replace(/^\.\//, "");
  if (normalized === ownedMathStyle) return [];
  let blocks;
  if (normalized.endsWith(".css")) blocks = [source];
  else {
    const withoutCode = normalized.endsWith(".md") ? stripMarkdownCode(source) : source;
    const markup = withoutCode.replace(/^---[\s\S]*?\n---/, "").replace(/<script\b[^>]*>[\s\S]*?<\/script\s*>/gi, "");
    blocks = [...markup.matchAll(/<style\b[^>]*>([\s\S]*?)<\/style\s*>/gi)].map((match) => match[1]);
  }
  return blocks.flatMap((block) => selectorsInCss(block).filter((selector) => mathSelector.test(selector)).map((selector) => ({
    code: "math-css-ownership", document: normalized,
    message: `Math-specific styles belong in ${ownedMathStyle}, not this file: ${selector}`,
  })));
}

function inspectSourceMathCss() {
  const sourceRoot = path.join(projectRoot, "src");
  const filenames = [".css", ".astro", ".md"].flatMap((suffix) => filesBelow(sourceRoot, suffix));
  return { files: filenames.length, issues: filenames.flatMap((filename) => inspectMathCssOwnership(fs.readFileSync(filename, "utf8"), path.relative(projectRoot, filename))) };
}

function displayMode(node) {
  for (let parent = node.parentNode; parent; parent = parent.parentNode) {
    if (classes(parent).has("katex-display")) return true;
    if (classes(parent).has("katex")) break;
  }
  return false;
}

const literalTextContainers = new Set(["code", "pre", "script", "style", "textarea", "noscript", "annotation"]);

function escapedAt(value, index) {
  let slashes = 0;
  for (let before = index - 1; before >= 0 && value[before] === "\\"; before -= 1) slashes += 1;
  return slashes % 2 === 1;
}

function looksLikeMath(source, delimiterLength) {
  const trimmed = source.trim();
  if (!trimmed || trimmed.includes("\0")) return false;
  if (/\\[A-Za-z]+|[_^]/.test(trimmed)) return true;
  // A prose/currency amount between two prices is not a delimited equation.
  if (/\b(?:and|or|per|each|from|to|costs?|month|year|hour|dollars?|million|billion|USD|EUR|GBP|CAD|AUD|CHF|JPY|CNY)\b/i.test(trimmed)) return false;
  if (/^\d[\d.\s]*(?:[+\-*/]\s*\d[\d.\s]*)+$/.test(trimmed)) return true;
  if (/^\d[\d,.]*(?:[KMBkmb])?(?:\s|\/|[-–—]|$)/.test(trimmed)) return delimiterLength === 2 && /^\d+(?:\.\d+)?$/.test(trimmed);
  if (/^[\p{L}]{1,12}(?:['′″]*)$/u.test(trimmed)) return true;
  return /\p{L}/u.test(trimmed) && /[=<>≤≥≈≠±×÷+*/{}()[\]|-]/.test(trimmed);
}

/** Conservative raw-delimiter alarm, not a general parser for prose/currency. */
export function findRawMathText(value) {
  const delimiters = [];
  for (let index = 0; index < value.length; index += 1) {
    if (value[index] !== "$" || escapedAt(value, index)) continue;
    let end = index + 1;
    while (value[end] === "$") end += 1;
    if (end - index <= 2) delimiters.push({ start: index, end, length: end - index });
    index = end - 1;
  }
  const candidates = [];
  for (let index = 0; index < delimiters.length - 1; index += 1) {
    const opening = delimiters[index];
    const closing = delimiters[index + 1];
    if (opening.length !== closing.length) continue;
    const source = value.slice(opening.end, closing.start);
    const limit = opening.length === 2 ? 2048 : 240;
    if (source.length <= limit && looksLikeMath(source, opening.length)) {
      candidates.push({ source, literal: value.slice(opening.start, closing.end) });
      index += 1; // The closing delimiter is not the next equation's opening.
    }
  }
  return candidates;
}

function unrenderedTextMath(tree) {
  const findings = [];
  function visit(node, excluded = false) {
    const skip = excluded || literalTextContainers.has(node.tagName) || classes(node).has("katex");
    if (!skip && node.nodeName === "#text") {
      for (const candidate of findRawMathText(node.value)) findings.push(candidate);
    }
    for (const child of node.childNodes ?? []) visit(child, skip);
    if (node.content) visit(node.content, skip);
  }
  visit(tree);
  return findings;
}

/** Inspect every rendered equation, including previously compiled/imported HTML. */
export function inspectMathMarkup(html, label = "document") {
  const tree = parse(html);
  const issues = [];
  const formulas = [];
  const add = (code, message, index) => issues.push({ code, document: label, ...(index === undefined ? {} : { formula: index }), message });
  for (const candidate of unrenderedTextMath(tree)) {
    add("raw-math-delimiters", `Likely unprocessed mathematical notation in rendered prose: ${candidate.literal}`);
  }
  for (const bad of nodesWhere(tree, (node) => classes(node).has("katex-error"))) {
    add("parse-error", attr(bad, "title") ?? text(bad));
  }
  for (const bad of nodesWhere(tree, (node) => classes(node).has("language-math") || classes(node).has("math-inline") || classes(node).has("math-display"))) {
    if (!nodesWhere(bad, (node) => classes(node).has("katex")).length) add("unrendered-math", "Math markup reached the output without being typeset.");
  }
  const rendered = nodesWhere(tree, (node) => classes(node).has("katex"));
  for (let index = 0; index < rendered.length; index += 1) {
    const node = rendered[index];
    const annotations = nodesWhere(node, (child) => child.tagName === "annotation" && attr(child, "encoding") === "application/x-tex");
    const accessible = nodesWhere(node, (child) => classes(child).has("katex-mathml"));
    const mathml = nodesWhere(node, (child) => child.tagName === "math");
    const visual = nodesWhere(node, (child) => classes(child).has("katex-html"));
    const source = annotations.length === 1 ? text(annotations[0]) : null;
    const isDisplay = displayMode(node);
    formulas.push({ source, display: isDisplay });
    if (annotations.length !== 1 || source === null || source.trim() === "") add("missing-tex-source", "Expected one non-empty application/x-tex source annotation.", index);
    if (accessible.length !== 1 || mathml.length !== 1 || visual.length !== 1 || attr(visual[0], "aria-hidden") !== "true") {
      add("accessibility-markup", "Expected one MathML representation and one aria-hidden visual representation.", index);
    }
    const old = nodesWhere(node, (child) => [...classes(child)].some((name) => legacyClasses.has(name)));
    if (old.length) add("legacy-renderer-class", "Equation uses pre-0.18 KaTeX base/strut/sizing classes with the 0.18 stylesheet contract.", index);
    if (source !== null) {
      try {
        const freshTree = parseFragment(renderMath(source, { displayMode: isDisplay }));
        const freshNode = nodesWhere(freshTree, (candidate) => classes(candidate).has("katex"))[0];
        if (!freshNode || JSON.stringify(canonical(freshNode, true)) !== JSON.stringify(canonical(node, true))) {
          add("stale-renderer-output", "Built math differs from the same source rendered with the current shared renderer and options.", index);
        }
      } catch (error) {
        add("invalid-tex", String(error.message ?? error), index);
      }
    }
  }
  return { tree, formulas, issues };
}

function packageFor(resolvedFile, expectedName) {
  let directory = path.dirname(resolvedFile);
  while (directory !== path.dirname(directory)) {
    const candidate = path.join(directory, "package.json");
    if (fs.existsSync(candidate)) {
      const metadata = JSON.parse(fs.readFileSync(candidate, "utf8"));
      if (metadata.name === expectedName) return { ...metadata, directory };
    }
    directory = path.dirname(directory);
  }
  throw new Error(`Cannot locate ${expectedName} metadata for ${resolvedFile}`);
}

/** Resolve dependencies from each actual caller, rather than trust a top-level npm listing. */
export function inspectDependencies() {
  const project = JSON.parse(fs.readFileSync(path.join(projectRoot, "package.json"), "utf8"));
  const rootKatex = packageFor(localRequire.resolve("katex"), "katex");
  const versions = { root: rootKatex.version };
  const issues = [];
  for (const caller of ["rehype-katex", "micromark-extension-math"]) {
    try {
      const callerRequire = createRequire(localRequire.resolve(caller));
      versions[caller] = packageFor(callerRequire.resolve("katex"), "katex").version;
    } catch (error) {
      issues.push({ code: "dependency-resolution", message: `${caller}: ${error.message}` });
    }
  }
  const cssPath = localRequire.resolve("katex/dist/katex.min.css");
  versions.stylesheet = packageFor(cssPath, "katex").version;
  for (const [caller, version] of Object.entries(versions)) {
    if (version !== rootKatex.version) issues.push({ code: "renderer-version-mismatch", message: `${caller} uses ${version}; root/CSS uses ${rootKatex.version}.` });
  }
  if (project.dependencies?.katex !== rootKatex.version) {
    issues.push({ code: "unpinned-renderer", message: `Pin katex to the exact installed version (${rootKatex.version}), not ${project.dependencies?.katex}.` });
  }
  const lock = JSON.parse(fs.readFileSync(path.join(projectRoot, "package-lock.json"), "utf8"));
  for (const [location, metadata] of Object.entries(lock.packages ?? {})) {
    if (/(^|\/)node_modules\/katex$/.test(location) && metadata.version !== rootKatex.version) {
      issues.push({ code: "lockfile-renderer-mismatch", message: `${location} locks ${metadata.version}; expected ${rootKatex.version}.` });
    }
  }
  const sourceCss = inspectSourceMathCss();
  issues.push(...sourceCss.issues);
  return { versions, mathStyleSourcesChecked: sourceCss.files, issues };
}

function localAsset(target, documentPath, distRoot) {
  if (/^(?:data:|https?:|\/\/|#)/i.test(target)) return null;
  const clean = decodeURIComponent(target.split(/[?#]/)[0]);
  const resolved = clean.startsWith("/") ? path.resolve(distRoot, `.${clean}`) : path.resolve(path.dirname(documentPath), clean);
  if (!resolved.startsWith(path.resolve(distRoot) + path.sep)) return null;
  return resolved;
}

function routeCategory(relativePath) {
  if (fs.existsSync(path.join(projectRoot, "public", relativePath))) return "public-static-html";
  const route = relativePath.replace(/\/index\.html$/, "").replace(/^index\.html$/, "").replace(/\.html$/, "");
  for (const candidate of [`${route}.astro`, `${route}/index.astro`]) {
    const filename = path.join(projectRoot, "src/pages", candidate);
    if (!fs.existsSync(filename)) continue;
    const source = fs.readFileSync(filename, "utf8");
    let importsMath = false;
    for (const match of source.matchAll(/from\s+["']([^"']+)\?raw["']/g)) {
      const imported = path.resolve(path.dirname(filename), match[1]);
      if (fs.existsSync(imported) && /class=["'][^"']*\bkatex\b/.test(fs.readFileSync(imported, "utf8"))) importsMath = true;
    }
    if (importsMath && /\brenderMath\b|<Math\b|\bkatex\b/.test(source)) return "astro-and-imported-math";
    if (importsMath) return "imported-generated-html";
    return "astro-renderer";
  }
  for (const root of ["src/content/posts", "src/pages"]) {
    if (fs.existsSync(path.join(projectRoot, root, `${route}.md`)) || fs.existsSync(path.join(projectRoot, root, `${route}/index.md`))) return "markdown";
  }
  return "other-generated-route";
}

export function auditBuild(distRoot) {
  const documents = [];
  const issues = [];
  const stylesheetCache = new Map();
  const assetCache = new Map();
  const rootKatex = packageFor(localRequire.resolve("katex"), "katex");
  const expectedFontDigests = new Set(filesBelow(path.join(rootKatex.directory, "dist/fonts"), "").map((filename) =>
    createHash("sha256").update(fs.readFileSync(filename)).digest("hex")));
  for (const filename of filesBelow(distRoot, ".html")) {
    const relative = path.relative(distRoot, filename).split(path.sep).join("/");
    const html = fs.readFileSync(filename, "utf8");
    const { tree, formulas, issues: mathIssues } = inspectMathMarkup(html, relative);
    issues.push(...mathIssues);
    if (formulas.length === 0) continue;
    const stylesheetNodes = nodesWhere(tree, (node) => node.tagName === "link" && (attr(node, "rel") ?? "").split(/\s+/).includes("stylesheet"));
    const cssFiles = [];
    for (const link of stylesheetNodes) {
      const href = attr(link, "href") ?? "";
      const cssFile = localAsset(href, filename, distRoot);
      if (!cssFile) {
        issues.push({ code: "nonlocal-stylesheet", document: relative, message: `Math pages must use versioned local stylesheets: ${href}` });
      } else if (!fs.existsSync(cssFile)) {
        issues.push({ code: "missing-stylesheet", document: relative, message: href });
      } else cssFiles.push(cssFile);
    }
    const inlineStyles = nodesWhere(tree, (node) => node.tagName === "style").map(text);
    let css = inlineStyles.join("\n");
    const cssInputs = inlineStyles.map((contents) => ({ filename, contents, label: `${relative} inline stylesheet` }));
    for (const cssFile of cssFiles) {
      if (!stylesheetCache.has(cssFile)) stylesheetCache.set(cssFile, fs.readFileSync(cssFile, "utf8"));
      const contents = stylesheetCache.get(cssFile);
      css += `\n${contents}`;
      cssInputs.push({ filename: cssFile, contents, label: path.relative(distRoot, cssFile) });
    }
    for (const input of cssInputs) {
      const { contents } = input;
      for (const match of contents.matchAll(/url\(\s*(?:"([^"]+)"|'([^']+)'|([^\s)]+))\s*\)/g)) {
        const target = match[1] ?? match[2] ?? match[3];
        const asset = localAsset(target, input.filename, distRoot);
        if (asset && !fs.existsSync(asset)) issues.push({ code: "missing-css-asset", document: relative, message: `${input.label} → ${target}` });
        if (asset && /KaTeX.*\.(?:woff2?|ttf)(?:[?#]|$)/i.test(target) && fs.existsSync(asset)) {
          if (!assetCache.has(asset)) assetCache.set(asset, createHash("sha256").update(fs.readFileSync(asset)).digest("hex"));
          if (!expectedFontDigests.has(assetCache.get(asset))) issues.push({ code: "math-font-integrity", document: relative, message: `${target} is not a font from the installed KaTeX distribution.` });
        }
        if (/KaTeX/i.test(target) && /^(?:https?:|\/\/)/i.test(target)) issues.push({ code: "remote-math-font", document: relative, message: target });
      }
    }
    for (const token of [".katex-sizing", ".katex-base", "KaTeX_Main", "@font-face"]) {
      if (!css.includes(token)) issues.push({ code: "missing-math-css", document: relative, message: `Loaded stylesheets lack ${token}.` });
    }
    documents.push({ file: relative, route: `/${relative.replace(/index\.html$/, "")}`, category: routeCategory(relative),
      equations: formulas.length, inline: formulas.filter((item) => !item.display).length, display: formulas.filter((item) => item.display).length,
      stylesheets: cssFiles.map((item) => path.relative(distRoot, item)) });
  }
  if (!documents.length) issues.push({ code: "no-math-output", message: "No rendered equations were found. Check that the complete website was built." });
  return { scannedHtml: filesBelow(distRoot, ".html").length, mathPages: documents.length,
    equations: documents.reduce((sum, item) => sum + item.equations, 0), verifiedLocalMathFonts: assetCache.size, documents, issues };
}

async function main() {
  const args = process.argv.slice(2);
  const dependencies = inspectDependencies();
  if (args.includes("--dependencies-only")) {
    console.log(JSON.stringify(dependencies, null, 2));
    process.exitCode = dependencies.issues.length ? 1 : 0;
    return;
  }
  const distFlag = args.indexOf("--dist");
  const distRoot = path.resolve(distFlag < 0 ? path.join(projectRoot, "dist") : args[distFlag + 1]);
  if (!fs.existsSync(distRoot)) throw new Error(`Build output does not exist: ${distRoot}`);
  const build = auditBuild(distRoot);
  const result = { versions: dependencies.versions, mathStyleSourcesChecked: dependencies.mathStyleSourcesChecked, ...build, issues: [...dependencies.issues, ...build.issues] };
  if (args.includes("--json")) console.log(JSON.stringify(result, null, 2));
  else {
    console.log(`Math audit: ${build.scannedHtml} HTML files; ${build.mathPages} math pages; ${build.equations} equations.`);
    console.log(`Renderer versions: ${JSON.stringify(dependencies.versions)}`);
    for (const document of build.documents) console.log(`  ${document.route} — ${document.equations} equations (${document.category})`);
    if (result.issues.length) {
      console.error(`FAILED: ${result.issues.length} math integrity issues.`);
      for (const issue of result.issues.slice(0, 40)) console.error(`  ${issue.document ?? "dependencies"}${issue.formula === undefined ? "" : ` #${issue.formula}`}: ${issue.code}: ${issue.message}`);
      if (result.issues.length > 40) console.error("  Use --json for the complete issue list.");
    } else console.log("PASS: shared-renderer output, accessible source, local styles and font assets are consistent.");
  }
  process.exitCode = result.issues.length ? 1 : 0;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((error) => { console.error(error.stack ?? error); process.exitCode = 1; });
}
