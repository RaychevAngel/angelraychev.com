import { parse } from 'parse5';
import { absoluteResourceUrl, normalizePath, PRIMARY_KINDS, RESOURCE_LABELS } from './publications.mjs';

const attr = (node, name) => node.attrs?.find(value => value.name === name)?.value;
const walk = (node) => [node, ...(node.childNodes ?? []).flatMap(walk)];
const text = (node) => node.nodeName === '#text' ? node.value : (node.childNodes ?? []).map(text).join('');

/** Homepage research entries expose the overview, not its resource inventory. */
export function inspectHomepagePublication(html, work) {
  const links = walk(parse(html)).filter(node => node.tagName === 'a'
    && normalizePath(attr(node, 'href') ?? '') === normalizePath(work.overview));
  if (!links.length) return []; // Companions and inline projects are not homepage entries.
  const issues = [];
  if (links.length !== 1) issues.push('Homepage overview must appear exactly once.');
  const title = links[0];
  if (text(title) !== work.title) issues.push('Homepage title differs from registry.');
  let entry = title.parentNode;
  while (entry && entry.tagName !== 'li') entry = entry.parentNode;
  if (!entry) return [...issues, 'Homepage overview must be a list entry.'];
  const visibleChildren = (entry.childNodes ?? []).filter(node => node.tagName
    || (node.nodeName === '#text' && node.value.trim()));
  const date = visibleChildren[1];
  if (visibleChildren.length !== 2 || visibleChildren[0] !== title
    || date?.tagName !== 'span' || !(attr(date, 'class') ?? '').split(/\s+/).includes('when')
    || !text(date).trim() || (date.childNodes ?? []).some(node => node.tagName)) {
    issues.push('Homepage entry must contain only its linked title and quiet update date.');
  }
  if (walk(entry).filter(node => node.tagName === 'a').length !== 1) {
    issues.push('Homepage entry must have one overview link, without artifact or record links.');
  }
  return issues;
}

/** Semantic checks deliberately include untagged author-written HTML. */
export function inspectPublicationSemantics(html, work) {
  const nodes = walk(parse(html));
  const issues = [];
  const title = nodes.filter(node => node.tagName === 'h1').map(text);
  if (JSON.stringify(title) !== JSON.stringify([work.title])) issues.push('Rendered title differs from registry display title.');
  const records = nodes.filter(node => attr(node, 'data-record')).map(node => ({kind: attr(node, 'data-record'), label: text(node).trim(), url: attr(node, 'href')}));
  const expectedRecords = work.records.map(({kind,label,url}) => ({kind,label,url}));
  if (JSON.stringify(records) !== JSON.stringify(expectedRecords)) issues.push('Publication record kind, label, destination or ordering differs from registry.');
  for (const node of nodes.filter(node => attr(node, 'data-record'))) {
    let inStatus = false;
    for (let ancestor = node.parentNode; ancestor; ancestor = ancestor.parentNode) if ((attr(ancestor, 'class') ?? '').split(/\s+/).includes('publication-status')) inStatus = true;
    if (!inStatus) issues.push('Publication record is outside the status line.');
  }
  for (const node of nodes.filter(node => node.tagName === 'a')) {
    const label = text(node).trim();
    const kind = PRIMARY_KINDS.find(kind => RESOURCE_LABELS[kind] === label);
    const obsolete = /^(?:Paper\s*\(PDF\)|Paper PDF|Report\s*\(PDF\)|Read the technical report|Code and evidence|Analysis and results)$/.test(label);
    if (!kind && !obsolete) continue;
    let generated = false;
    for (let ancestor = node.parentNode; ancestor; ancestor = ancestor.parentNode) {
      if (attr(ancestor, 'data-publication') === work.id) generated = true;
    }
    if (!generated || obsolete) issues.push(`Hand-written or obsolete primary link label outside generated header: ${label}.`);
  }
  if (work.primary.pdf) {
    const values = name => nodes.filter(node => node.tagName === 'meta' && attr(node, 'name') === name).map(node => attr(node, 'content'));
    const check = (name, expected) => { if (JSON.stringify(values(name)) !== JSON.stringify(expected)) issues.push(`Scholarly metadata ${name} differs from selected manuscript.`); };
    check('citation_title', [work.manuscriptTitle]);
    check('citation_author', work.authors);
    check('citation_pdf_url', [absoluteResourceUrl(work.primary.pdf.url)]);
    check('citation_publication_date', work.manuscriptDate ? [work.manuscriptDate.replaceAll('-', '/')] : []);
    for (const [kind,name,segment] of [['arxiv','citation_arxiv_id','/abs/'],['journal','citation_doi','doi.org/']]) check(name, work.records.filter(record=>record.kind===kind).map(record=>record.url.split(segment)[1]));
    const structured = nodes.filter(node=>node.tagName==='script' && attr(node,'type')==='application/ld+json');
    try {
      if (structured.length !== 1) throw new Error('Expected one scholarly JSON-LD record.');
      const data = JSON.parse(text(structured[0]));
      if (data.name !== work.manuscriptTitle || data.encoding?.contentUrl !== absoluteResourceUrl(work.primary.pdf.url)
        || data.datePublished !== work.manuscriptDate || data.dateModified !== work.manuscriptModified
        || JSON.stringify(data.author?.map(author=>author.name)) !== JSON.stringify(work.authors)) issues.push('Scholarly JSON-LD differs from the selected manuscript identity or dates.');
    } catch { issues.push('Missing or invalid scholarly JSON-LD.'); }
  }
  return issues;
}
