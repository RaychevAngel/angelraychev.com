/** Apply one table contract to Markdown, Astro, generated fragments and public HTML. */
import fs from "node:fs";
import path from "node:path";
import { normalizeTableHtml } from "../src/lib/tables.mjs";

const root = path.resolve(process.argv[2] ?? "dist");
function files(directory) {
  return fs.readdirSync(directory, { withFileTypes: true }).flatMap((entry) => entry.isDirectory() ? files(path.join(directory, entry.name)) : entry.name.endsWith(".html") ? [path.join(directory, entry.name)] : []);
}
let tables = 0;
let changed = 0;
const htmlFiles = files(root);
for (const filename of htmlFiles) {
  const source = fs.readFileSync(filename, "utf8");
  if (!/<table\b/i.test(source)) continue;
  const result = normalizeTableHtml(source, { label: path.relative(root, filename) });
  tables += result.tables;
  if (result.changed) { fs.writeFileSync(filename, result.html); changed += 1; }
}
console.log(`Prepared ${tables} data tables across ${htmlFiles.length} HTML files; ${changed} files normalized without rewriting table content.`);
