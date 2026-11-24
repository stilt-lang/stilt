// The website, built from the repository into target/site by `just site` (site/README.md).

import tailwindcss from "@tailwindcss/vite";
import { defineConfig } from "astro/config";
import { checks } from "./src/lib/checks.ts";

export default defineConfig({
  outDir: "../target/site",
  trailingSlash: "always",
  build: { format: "directory" },
  prefetch: { prefetchAll: true, defaultStrategy: "hover" },
  devToolbar: { enabled: false },
  integrations: [checks()],
  vite: { plugins: [tailwindcss()] },
});
