import { parseFragment, serialize } from "parse5";
import { tableAttribute, tableText, walkTableTree } from "./tables.mjs";

export function readRunningRecord(html, year) {
  const nodes = [];
  walkTableTree(parseFragment(html), (node) => nodes.push(node));
  const chronology = nodes.find((node) => tableAttribute(node, "id") === "completed-session-chronology");
  const summary = nodes.find((node) => tableAttribute(node, "id") === "current-cycle-summary");
  const body = chronology?.childNodes.find((node) => node.tagName === "tbody");
  if (!body || !summary) throw new Error("The current running record needs a chronology and cycle summary.");

  const sessions = body.childNodes.filter((node) => node.tagName === "tr").map((row) => {
    const cells = row.childNodes.filter((node) => node.tagName === "td");
    const [dateCell, sessionCell, resultCell, observationCell] = cells;
    const dateLink = dateCell?.childNodes.find((node) => node.tagName === "a");
    const fragment = dateLink && tableAttribute(dateLink, "href");
    const date = dateLink && tableText(dateLink);
    const timestamp = Date.parse(`${date} ${year} UTC`);
    if (cells.length !== 4 || !fragment?.startsWith("#") || !Number.isFinite(timestamp)
      || !nodes.some((node) => tableAttribute(node, "id") === fragment.slice(1))) {
      throw new Error(`Invalid completed running session: ${date ?? "missing date"}.`);
    }
    return {
      date,
      timestamp,
      href: `/running/record/${year}/${fragment}`,
      session: tableText(sessionCell),
      resultHtml: serialize(resultCell),
      observation: tableText(observationCell),
      benchmark: tableAttribute(row, "data-event-benchmark") !== undefined,
    };
  });
  if (!sessions.length) throw new Error("The completed running chronology is empty.");

  sessions.sort((a, b) => a.timestamp - b.timestamp);
  return { sessions, summaryHtml: serialize(summary) };
}
