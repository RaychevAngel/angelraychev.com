import registry from '../data/publications.json' with { type: 'json' };

export const PRIMARY_KINDS = ['pdf', 'code', 'lean'];
export const RESOURCE_LABELS = Object.freeze({
  pdf: 'PDF', code: 'Code', lean: 'Lean', arxiv: 'arXiv', journal: 'Journal',
  latex: 'LaTeX', citation: 'Citation', documentation: 'Documentation',
  releases: 'Releases', versions: 'Versions', evidence: 'Evidence',
  supplement: 'Supplement', archive: 'Archive', models: 'Models',
  source: 'Source', related: 'Related work', data: 'Data',
});

export const publications = registry.works;
export const absoluteResourceUrl = (url) => new URL(url, 'https://angelraychev.com').href;
export const normalizePath = (path) => path.replace(/\/+$/, '') || '/';
export const publicationById = (id) => publications.find((work) => work.id === id);
export const publicationForPath = (path) => publications.find((work) =>
  !work.overview.includes('#') && normalizePath(work.overview) === normalizePath(path));
export const primaryResources = (work) => PRIMARY_KINDS.flatMap((kind) =>
  work?.primary?.[kind] ? [{ ...work.primary[kind], kind, label: RESOURCE_LABELS[kind] }] : []);
export const supportingResources = (work) => (work?.resources ?? []).map((resource) => ({
  ...resource, label: resource.label ?? RESOURCE_LABELS[resource.kind],
}));

export function validatePublicationRegistry(data) {
  const issues = [];
  const check = (condition, message) => { if (!condition) issues.push(message); };
  check(data?.schemaVersion === 1, 'Unsupported publication registry schema.');
  check(Array.isArray(data?.works), 'Registry works must be an array.');
  const ids = new Set(), overviews = new Set();
  for (const work of data?.works ?? []) {
    const prefix = work.id ?? '(missing ID)';
    check(typeof work.id === 'string' && /^[a-z0-9-]+$/.test(work.id), `${prefix}: invalid ID.`);
    check(!ids.has(work.id), `${prefix}: duplicate ID.`); ids.add(work.id);
    check(typeof work.title === 'string' && work.title.trim(), `${prefix}: title is required.`);
    check(typeof work.overview === 'string' && work.overview.startsWith('/') && !work.overview.startsWith('//'), `${prefix}: overview must be a website path.`);
    check(!overviews.has(work.overview), `${prefix}: duplicate overview.`); overviews.add(work.overview);
    check(typeof work.kind === 'string' && typeof work.status === 'string', `${prefix}: kind and status are required.`);
    check(Array.isArray(work.authors) && work.authors.every(author => typeof author === 'string' && author.trim()), `${prefix}: authors must be explicit strings.`);
    check(work.primary && typeof work.primary === 'object', `${prefix}: primary must be an object.`);
    check(Object.keys(work.primary ?? {}).every(kind => PRIMARY_KINDS.includes(kind)), `${prefix}: unrecognized primary resource.`);
    const recordKinds = new Set();
    for (const record of work.records ?? []) {
      check(['arxiv', 'journal'].includes(record.kind), `${prefix}: invalid publication record.`);
      check(!recordKinds.has(record.kind), `${prefix}: duplicate publication record.`); recordKinds.add(record.kind);
      check(typeof record.label === 'string' && record.label.trim(), `${prefix}: record label required.`);
      const pattern = record.kind === 'arxiv' ? /^https:\/\/arxiv\.org\/abs\/\d{4}\.\d{4,5}(?:v\d+)?$/ : /^https:\/\/doi\.org\/10\./;
      check(pattern.test(record.url), `${prefix}: ${record.kind} must open its publication record.`);
    }
    for (const [kind, resource] of Object.entries(work.primary ?? {})) {
      let url;
      try { url = new URL(resource.url, 'https://angelraychev.com'); } catch { issues.push(`${prefix}: invalid ${kind} URL.`); continue; }
      check(url.protocol === 'https:', `${prefix}: ${kind} must use HTTPS or a local path.`);
      check(!resource.label, `${prefix}: primary labels are fixed, not overridable.`);
      if (kind === 'pdf') {
        check(typeof work.manuscriptTitle === 'string' && work.manuscriptTitle.trim(), `${prefix}: exact manuscript title must be identified separately from overview title.`);
        check(/\.pdf$/i.test(url.pathname) || (url.hostname === 'arxiv.org' && /^\/pdf\/\d{4}\.\d{4,5}v\d+$/.test(url.pathname)), `${prefix}: PDF must open a PDF; arXiv PDF must pin a version.`);
        check(typeof resource.version === 'string' && resource.version.trim(), `${prefix}: PDF version must be identified.`);
      }
      if (kind === 'code') check(url.hostname === 'github.com' && /^\/[^/]+\/[^/]+\/?$/.test(url.pathname), `${prefix}: Code must open a project repository, not a PR, binary release or file.`);
      if (kind === 'lean') check(!/\.(?:zip|lean|json|tar|gz)$/i.test(url.pathname), `${prefix}: Lean must open a scope/reproduction guide, not a raw archive.`);
    }
    const destinations = new Set();
    for (const resource of work.resources ?? []) {
      check(Boolean(RESOURCE_LABELS[resource.kind]) && !PRIMARY_KINDS.includes(resource.kind), `${prefix}: invalid supporting resource kind.`);
      check(typeof resource.url === 'string' && resource.url.trim(), `${prefix}: supporting resource URL required.`);
      try { check(new URL(resource.url, 'https://angelraychev.com').protocol === 'https:', `${prefix}: supporting URL must use HTTPS or a local path.`); } catch { issues.push(`${prefix}: invalid supporting URL.`); }
      check(!destinations.has(resource.url), `${prefix}: duplicate supporting resource destination.`); destinations.add(resource.url);
    }
  }
  return issues;
}
