import { getCollection } from "astro:content";

const SITE = "https://angelraychev.com";
const escapeXml = (value: string) => value.replace(/&/g, "&amp;")
  .replace(/</g, "&lt;").replace(/>/g, "&gt;")
  .replace(/"/g, "&quot;").replace(/'/g, "&apos;");

export async function GET() {
  // Match the public homepage/RSS collection, never enumerate data directories
  // or unpublished drafts merely because they exist in the build.
  const posts = (await getCollection("posts"))
    .filter((post) => !post.data.draft)
    .sort((a, b) => a.id.localeCompare(b.id));

  const xml = `<?xml version="1.0" encoding="UTF-8"?>
<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">
  <url><loc>${SITE}/</loc></url>
${posts.map((post) => `  <url><loc>${escapeXml(new URL(`/${post.id}/`, SITE).href)}</loc><lastmod>${post.data.updated.toISOString().slice(0, 10)}</lastmod></url>`).join("\n")}
</urlset>`;

  return new Response(xml, {
    headers: { "Content-Type": "application/xml; charset=utf-8" },
  });
}
