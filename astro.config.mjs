import { defineConfig } from "astro/config";
import fs from "node:fs";
import path from "node:path";

// Astro's dev server (Vite) does not resolve "/dir/" to "/dir/index.html" for
// files served from public/. Static hosts (GitHub Pages) do. Without this,
// report links 404 in local preview but work in production.
function publicDirectoryIndex() {
  const publicDir = path.resolve("public");
  return {
    name: "public-directory-index",
    configureServer(server) {
      server.middlewares.use((req, _res, next) => {
        const url = (req.url ?? "").split("?")[0];
        if (url.endsWith("/")) {
          const candidate = path.resolve(publicDir, "." + url, "index.html");
          // guard against path traversal escaping public/
          if (candidate.startsWith(publicDir + path.sep) && fs.existsSync(candidate)) {
            req.url = url + "index.html";
          }
        }
        next();
      });
    },
  };
}

export default defineConfig({
  site: "https://angelraychev.com",
  markdown: { shikiConfig: { theme: "github-light" } },
  vite: { plugins: [publicDirectoryIndex()] },
});
