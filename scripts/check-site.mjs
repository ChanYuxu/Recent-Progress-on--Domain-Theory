import { existsSync, readFileSync, readdirSync, statSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { dirname, join, normalize, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const failures = [];

const walk = (directory) => readdirSync(directory, { withFileTypes: true }).flatMap((entry) => {
  const fullPath = join(directory, entry.name);
  if (entry.isDirectory()) {
    return entry.name === '.git' || entry.name === 'tmp' ? [] : walk(fullPath);
  }
  return [fullPath];
});

const htmlFiles = walk(root).filter((path) => path.endsWith('.html'));
const localTarget = (htmlPath, value) => {
  const cleanValue = value.split(/[?#]/, 1)[0];
  if (!cleanValue || /^(?:[a-z]+:|\/\/|#)/i.test(value)) {
    return null;
  }
  if (cleanValue.startsWith('/')) {
    failures.push(`${htmlPath}: root-absolute local link is not project-site safe: ${value}`);
    return null;
  }
  return normalize(resolve(dirname(htmlPath), decodeURIComponent(cleanValue)));
};

for (const htmlPath of htmlFiles) {
  const html = readFileSync(htmlPath, 'utf8');
  const references = [...html.matchAll(/\b(?:href|src|data)="([^"]+)"/g)].map((match) => match[1]);
  for (const reference of references) {
    const target = localTarget(htmlPath, reference);
    if (!target) {
      continue;
    }
    const candidate = existsSync(target) && statSync(target).isDirectory() ? join(target, 'index.html') : target;
    if (!existsSync(candidate)) {
      failures.push(`${htmlPath}: missing local target ${reference}`);
    }
  }
}

const registry = JSON.parse(readFileSync(join(root, 'data', 'papers.json'), 'utf8'));
const publishedDates = registry.papers.map((paper) => paper.published);
const sortedDates = [...publishedDates].sort((left, right) => right.localeCompare(left));
if (publishedDates.join('\n') !== sortedDates.join('\n')) {
  failures.push('data/papers.json is not sorted by descending publication date');
}

for (const paper of registry.papers) {
  const paperRoot = join(root, paper.path);
  const artifacts = paper.artifacts ?? ['paper.pdf', 'lean-source.zip'];
  const sourceTree = paper.sourceTree === undefined ? true : paper.sourceTree;
  if (typeof sourceTree !== 'boolean') {
    failures.push(`${paper.slug}: sourceTree must be a boolean`);
  }
  if (sourceTree === false && !artifacts.some((artifact) => artifact.endsWith('.zip'))) {
    failures.push(`${paper.slug}: a ZIP-only entry must list a Lean archive`);
  }
  const sourcePaths = sourceTree === false ? [] : ['lean', 'lean/README.md'];
  for (const required of ['index.html', ...artifacts, ...sourcePaths]) {
    if (!existsSync(join(paperRoot, required))) {
      failures.push(`${paper.slug}: missing ${required}`);
    }
  }

  const article = readFileSync(join(paperRoot, 'index.html'), 'utf8');
  if (!article.includes(`data-paper-slug="${paper.slug}"`)) {
    failures.push(`${paper.slug}: body slug does not match the registry`);
  }
  if (!article.includes(`content="${paper.published}"`)) {
    failures.push(`${paper.slug}: publication date does not match the registry`);
  }

  for (const artifact of artifacts) {
    const artifactPath = join(paperRoot, artifact);
    if (!existsSync(artifactPath)) {
      continue;
    }
    const digest = createHash('sha256').update(readFileSync(artifactPath)).digest('hex');
    if (!article.includes(digest)) {
      failures.push(`${paper.slug}: ${artifact} SHA-256 is missing or stale in the article`);
    }
  }
}

if (failures.length > 0) {
  console.error(failures.join('\n'));
  process.exitCode = 1;
} else {
  console.log(`Validated ${htmlFiles.length} HTML pages and ${registry.papers.length} paper packages.`);
}
