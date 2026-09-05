import { getCollection } from "astro:content";

const SITE = "https://angelraychev.com";
const esc = (s: string) =>
  s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

export async function GET() {
  const posts = (await getCollection("posts"))
    .filter((p) => !p.data.draft)
    .sort((a, b) => b.data.updated.valueOf() - a.data.updated.valueOf());

  const xml = `<?xml version="1.0" encoding="UTF-8"?>
<rss version="2.0" xmlns:atom="http://www.w3.org/2005/Atom">
  <channel>
    <title>Angel Ivanov Raychev</title>
    <link>${SITE}</link>
    <description>Angel Ivanov Raychev</description>
    <language>en</language>
    <atom:link href="${SITE}/rss.xml" rel="self" type="application/rss+xml" />
${posts
  .map(
    (p) => `    <item>
      <title>${esc(p.data.title)}</title>
      <link>${SITE}/${p.id}</link>
      <guid isPermaLink="true">${SITE}/${p.id}</guid>
      <description>${esc(p.data.description ?? "")}</description>
      <pubDate>${p.data.updated.toUTCString()}</pubDate>
    </item>`
  )
  .join("\n")}
  </channel>
</rss>`;

  return new Response(xml, { headers: { "Content-Type": "application/xml; charset=utf-8" } });
}
