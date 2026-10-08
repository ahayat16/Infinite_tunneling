import { createRoot } from 'react-dom/client';
import { ReviewSite } from '../components/review-site';
import bootstrap from '../content/generated/bootstrap.json';
import '../app/globals.css';
import 'katex/dist/katex.min.css';

type EmbeddedFile = { text: string; type: string };
const files: Record<string, EmbeddedFile> = JSON.parse(
  document.getElementById('offline-files')!.textContent!,
);
const base = 'https://infinite-zero.invalid/';
const nativeFetch = window.fetch.bind(window);

function fileKey(path: string) {
  return decodeURIComponent(new URL(path, base).pathname.slice(1));
}

// The reader's existing requests are served from the embedded snapshot.
window.fetch = async (input, init) => {
  const path = typeof input === 'string' ? input : input instanceof URL ? input.href : input.url;
  if (/^(https?:|data:|blob:)/i.test(path)) return nativeFetch(input, init);
  if (init?.signal?.aborted) throw new DOMException('Aborted', 'AbortError');
  const file = files[fileKey(path)];
  return file
    ? new Response(file.text, { headers: { 'Content-Type': file.type } })
    : new Response('File unavailable in this snapshot.', { status: 404 });
};

// Source links and downloads use the same embedded files as the reader.
const objectUrls = new Map<string, string>();
document.addEventListener('click', (event) => {
  const link = event.target instanceof Element ? event.target.closest('a') : null;
  const href = link?.getAttribute('href');
  if (!link || !href || href.startsWith('#') || /^(?:[a-z]+:|\/\/)/i.test(href)) return;
  const key = fileKey(href);
  const file = files[key];
  if (!file) return;
  let url = objectUrls.get(key);
  if (!url) {
    url = URL.createObjectURL(new Blob([file.text], { type: file.type }));
    objectUrls.set(key, url);
  }
  link.href = url;
  if (link.hasAttribute('download')) link.download = key.split('/').pop()!;
}, true);

createRoot(document.getElementById('root')!).render(<ReviewSite bootstrap={bootstrap} />);
