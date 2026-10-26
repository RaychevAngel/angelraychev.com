#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createHash } from 'node:crypto';
import { parse } from 'parse5';
import registry from '../src/data/publications.json' with { type: 'json' };
import { primaryResources, supportingResources, validatePublicationRegistry } from '../src/lib/publications.mjs';
import { inspectHomepagePublication, inspectPublicationSemantics } from '../src/lib/publication-html.mjs';

const root = fileURLToPath(new URL('../', import.meta.url));
const issues = validatePublicationRegistry(registry);
for (const work of registry.works.filter(work => work.artifactManifest)) {
  const manifestPath = path.join(root, 'public', work.artifactManifest);
  try {
    const manifest = JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
    const artifacts = Array.isArray(manifest.artifacts) ? manifest.artifacts : Object.entries(manifest.artifacts).map(([file,value])=>({file,...value}));
    for (const artifact of artifacts) {
      const filename = path.join(path.dirname(manifestPath), artifact.file);
      const hash = createHash('sha256').update(fs.readFileSync(filename)).digest('hex');
      if (hash !== artifact.sha256) issues.push(`${work.id}: stale artifact hash for ${artifact.file}.`);
    }
  } catch (error) { issues.push(`${work.id}: artifact manifest cannot be verified: ${error.message}`); }
}
const documents = new Map();
const attr = (node, name) => node.attrs?.find(attribute => attribute.name === name)?.value;
const children = node => node.childNodes ?? [];
const all = (node, predicate) => [...(predicate(node) ? [node] : []), ...children(node).flatMap(child => all(child, predicate))];
const content = node => node.nodeName === '#text' ? node.value : children(node).map(content).join('');
function documentFor(url) {
  const pathname = decodeURIComponent(new URL(url, 'https://angelraychev.com').pathname);
  const target = path.resolve(root, 'dist', `.${pathname}`);
  const filename = fs.existsSync(target) && fs.statSync(target).isFile() ? target : path.join(target, 'index.html');
  if (!fs.existsSync(filename)) return null;
  if (!documents.has(filename)) documents.set(filename, parse(fs.readFileSync(filename, 'utf8')));
  return documents.get(filename);
}
function checkDestination(url, context) {
  const resolved = new URL(url, 'https://angelraychev.com');
  if (resolved.origin !== 'https://angelraychev.com') return;
  const target = path.resolve(root, 'dist', `.${decodeURIComponent(resolved.pathname)}`);
  if (!fs.existsSync(target)) { issues.push(`${context}: missing local destination ${url}`); return; }
  if (resolved.hash) {
    const doc = documentFor(url);
    if (!doc || !all(doc, node => attr(node, 'id') === decodeURIComponent(resolved.hash.slice(1))).length) issues.push(`${context}: missing anchor ${url}`);
  }
}

if (!process.argv.includes('--source-only') && !issues.length) {
  for (const work of registry.works) {
    checkDestination(work.overview, work.id);
    for (const resource of [...primaryResources(work), ...supportingResources(work)]) checkDestination(resource.url, `${work.id}/${resource.kind}`);
    if (work.overview.includes('#')) continue;
    const doc = documentFor(work.overview);
    if (!doc) continue;
    const filename = path.join(root, 'dist', work.overview, 'index.html');
    issues.push(...inspectPublicationSemantics(fs.readFileSync(filename, 'utf8'), work).map(issue => `${work.id}: ${issue}`));
    const headers = all(doc, node => attr(node, 'data-publication') === work.id);
    if (headers.length !== 1) { issues.push(`${work.id}: expected exactly one generated publication header.`); continue; }
    const actual = all(headers[0], node => attr(node, 'data-resource')).map(node => ({kind: attr(node, 'data-resource'), label: content(node).trim(), url: attr(node, 'href')}));
    const expected = primaryResources(work).map(({kind, label, url}) => ({kind, label, url}));
    if (JSON.stringify(actual) !== JSON.stringify(expected)) issues.push(`${work.id}: primary labels, destinations or ordering differ from registry.`);
    const recordNodes = all(headers[0], node => attr(node, 'data-record'));
    if (recordNodes.length !== work.records.length) issues.push(`${work.id}: publication records differ from registry.`);
    const sections = all(doc, node => attr(node, 'data-resource-section') === work.id);
    if (sections.length !== (work.resources.length ? 1 : 0)) issues.push(`${work.id}: expected one generated Resources section.`);
    if (sections.length) {
      const actualSupport = all(sections[0], node => attr(node, 'data-supporting-resource')).map(node => ({kind: attr(node, 'data-supporting-resource'), label: content(node).trim(), url: attr(node, 'href')}));
      const expectedSupport = supportingResources(work).map(({kind, label, url}) => ({kind, label, url}));
      if (JSON.stringify(actualSupport) !== JSON.stringify(expectedSupport)) issues.push(`${work.id}: supporting resources differ from registry.`);
    }
    const ids = all(doc, node => Boolean(attr(node, 'id'))).map(node => attr(node, 'id'));
    if (new Set(ids).size !== ids.length) issues.push(`${work.id}: duplicate HTML IDs.`);
    const headings = all(doc, node => node.tagName === 'h1');
    if (headings.length !== 1) issues.push(`${work.id}: expected one page title.`);
    const article = all(doc, node => node.tagName === 'article')[0];
    const elements = children(article ?? {}).filter(node => node.tagName);
    if (elements[0]?.tagName !== 'h1' || attr(elements[1] ?? {}, 'data-publication') !== work.id) issues.push(`${work.id}: header is not immediately after title.`);
  }
  const homepageHtml = fs.readFileSync(path.join(root, 'dist', 'index.html'), 'utf8');
  for (const work of registry.works) {
    issues.push(...inspectHomepagePublication(homepageHtml, work).map(issue => `${work.id}: ${issue}`));
  }
}

console.log(JSON.stringify({works: registry.works.length, mode: process.argv.includes('--source-only') ? 'registry' : 'built site', documentsChecked: documents.size, issues}, null, 2));
if (issues.length) process.exitCode = 1;
