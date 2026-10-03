import { sites } from '@openai/sites-vite-plugin';
import tailwindcss from '@tailwindcss/postcss';
import vinext from 'vinext';
import { defineConfig } from 'vite';
// Static reader: no worker, database or account is needed.
export default defineConfig({
  base: './',
  css: { postcss: { plugins: [tailwindcss()] } },
  server: { watch: { useFsEvents: false, usePolling: true } },
  plugins: [vinext(), sites()],
});
