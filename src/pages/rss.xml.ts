import { getCollection } from "astro:content";
import { reports } from "../data/reports";

const SITE = "https://angelraychev.com";
const esc = (s: string) =>
  s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

export async function GET() {
  const posts = (await getCollection("posts")).filter((p) => !p.data.draft);
  const items = [
    ...reports.map((r) => ({ title: r.title, description: r.description, link: `${SITE}/reports/${r.slug}/`, date: new Date(r.date) })),
    ...posts.map((p) => ({ title: p.data.title, description: p.data.description ?? "", link: `${SITE}/writing/${p.id}`, date: p.data.date })),
  ].sort((a, b) => b.date.valueOf() - a.date.valueOf());

  const xml = `<?xml version="1.0" encoding="UTF-8"?>
<rss version="2.0" xmlns:atom="http://www.w3.org/2005/Atom">
  <channel>
    <title>Angel Raychev</title>
    <link>${SITE}</link>
    <description>Writing on physical capability, longevity, and what survives checking.</description>
    <language>en</language>
    <atom:link href="${SITE}/rss.xml" rel="self" type="application/rss+xml" />
${items
  .map(
    (i) => `    <item>
      <title>${esc(i.title)}</title>
      <link>${i.link}</link>
      <guid isPermaLink="true">${i.link}</guid>
      <description>${esc(i.description)}</description>
      <pubDate>${i.date.toUTCString()}</pubDate>
    </item>`
  )
  .join("\n")}
  </channel>
</rss>`;

  return new Response(xml, { headers: { "Content-Type": "application/xml; charset=utf-8" } });
}
