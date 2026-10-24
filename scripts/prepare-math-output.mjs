/** Normalize the legacy static archive without altering its frozen source. */
import fs from "node:fs";
import path from "node:path";
import { rerenderMathHtml } from "../src/lib/math.mjs";
import { restorePrincessProofTableHeaders } from "../src/lib/princess-proof-tables.mjs";

const dist = path.resolve("dist");
const archive = "princess/archive/2026-09-13-combined/proofs.html";
const source = fs.readFileSync(path.join("public", archive), "utf8");
const home = fs.readFileSync(path.join(dist, "index.html"), "utf8");
const styleLinks = [...home.matchAll(/<link\b[^>]*rel="stylesheet"[^>]*>/g)].map((match) => match[0]).join("\n");
const moduleScripts = [...home.matchAll(/<script\b[^>]*type="module"[^>]*>[\s\S]*?<\/script>/g)].map((match) => match[0]).join("\n");
const themeInitialization = home.match(/<script>[^<]*localStorage[^<]*<\/script>/)?.[0] ?? "";
const themeToggle = home.match(/<button\b[^>]*data-theme-toggle[^>]*>[\s\S]*?<\/button>/)?.[0] ?? "";
if (!styleLinks) throw new Error("Cannot find the shared site stylesheets for archived mathematics.");
const content = restorePrincessProofTableHeaders(rerenderMathHtml(source, { label: "archived rectangle manuscript" }));
const html = `<!doctype html>
<html lang="en" data-theme="light"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="robots" content="noindex,follow">
<title>Archived rectangle search proofs — Angel Ivanov Raychev</title>
<link rel="canonical" href="https://angelraychev.com/${archive}">
${styleLinks}
${themeInitialization}
${moduleScripts}
</head><body><div class="wrap">
<header class="site"><a href="/">Angel Ivanov Raychev</a>${themeToggle}</header>
<main><article>${content}</article></main>
<footer class="site"><a href="/princess/">Current rectangle search research</a></footer>
</div></body></html>`;
fs.writeFileSync(path.join(dist, archive), html);
console.log("Prepared legacy math archive with matching local styles and fresh shared-renderer output.");
