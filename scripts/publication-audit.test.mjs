import test from 'node:test';
import assert from 'node:assert/strict';
import registry from '../src/data/publications.json' with {type: 'json'};
import { validatePublicationRegistry, primaryResources, publicationForPath } from '../src/lib/publications.mjs';
import { inspectPublicationSemantics } from '../src/lib/publication-html.mjs';

test('current registry has valid, distinct publication identities', () => assert.deepEqual(validatePublicationRegistry(registry), []));
test('primary ordering is independent of object authoring order', () => assert.deepEqual(primaryResources({primary:{lean:{url:'/guide/'},pdf:{url:'/paper.pdf'},code:{url:'https://github.com/a/b'}}}).map(r=>r.label), ['PDF','Code','Lean']));
test('overview lookup does not attach main resources to descendants or fragments', () => {
  assert.equal(publicationForPath('/princess')?.id, 'capture-time');
  assert.equal(publicationForPath('/princess/extensions/')?.id, 'capture-time-extensions');
  assert.equal(publicationForPath('/princess/proofs/'), undefined);
  assert.equal(publicationForPath('/model-specialization-and-training-agents/').id, 'model-specialization');
});
for (const [name, mutate, expected] of [
  ['PDF cannot be abstract record', data=>{data.works[1].primary.pdf.url='https://arxiv.org/abs/2610.30765';}, /PDF must open a PDF/],
  ['arXiv PDF must pin version', data=>{data.works[1].primary.pdf.url='https://arxiv.org/pdf/2610.30765';}, /pin a version/],
  ['arXiv record cannot be PDF', data=>{data.works[1].records[0].url='https://arxiv.org/pdf/2610.30765v1';}, /publication record/],
  ['Code cannot be a PR', data=>{data.works[1].primary.code.url='https://github.com/a/b/pull/1';}, /project repository/],
  ['Lean cannot be ZIP', data=>{data.works[8].primary.lean.url='/proofs.zip';}, /scope\/reproduction guide/],
  ['PDF version cannot be omitted', data=>{delete data.works[1].primary.pdf.version;}, /version must be identified/],
  ['primary labels cannot drift', data=>{data.works[1].primary.pdf.label='Read paper';}, /not overridable/],
  ['duplicate identities rejected', data=>{data.works.push(data.works[0]);}, /duplicate ID/],
]) test(name, () => {
  const data = structuredClone(registry); mutate(data);
  assert.ok(validatePublicationRegistry(data).some(issue=>expected.test(issue)));
});

const specimen = registry.works.find(work=>work.id==='generative-reward-models');
const scholarly = {name:specimen.manuscriptTitle, author:specimen.authors.map(name=>({name})), datePublished:specimen.manuscriptDate, encoding:{contentUrl:specimen.primary.pdf.url}};
const validHtml = `<html><head><meta name="citation_title" content="${specimen.manuscriptTitle}">${specimen.authors.map(author=>`<meta name="citation_author" content="${author}">`).join('')}<meta name="citation_publication_date" content="2026/10/22"><meta name="citation_arxiv_id" content="2610.30765"><meta name="citation_pdf_url" content="${specimen.primary.pdf.url}"><script type="application/ld+json">${JSON.stringify(scholarly)}</script></head><body><article><h1>${specimen.title}</h1><div data-publication="${specimen.id}"><p class="publication-status"><a data-record="arxiv" href="${specimen.records[0].url}">arXiv:2610.30765</a></p><a data-resource="pdf" href="${specimen.primary.pdf.url}">PDF</a><a data-resource="code" href="${specimen.primary.code.url}">Code</a></div></article></body></html>`;
test('rendered semantic specimen is accepted', () => assert.deepEqual(inspectPublicationSemantics(validHtml, specimen), []));
test('same-count arXiv record substitution is rejected', () => assert.ok(inspectPublicationSemantics(validHtml.replace(specimen.records[0].url, specimen.primary.pdf.url), specimen).some(issue=>/record/.test(issue))));
test('untagged hand-written primary row cannot bypass registry', () => assert.ok(inspectPublicationSemantics(validHtml.replace('</article>','<p><a href="/proofs.zip">Code</a> · <a href="https://arxiv.org/abs/2610.30765">PDF</a></p></article>'), specimen).some(issue=>/Hand-written/.test(issue))));
test('metadata preserves exact manuscript title and publication date', () => {
  const mutated = validHtml.replace('<meta name="citation_title" content="Scaling Laws for Generative Reward Models">', '<meta name="citation_title" content="Short overview title">').replace('<meta name="citation_publication_date" content="2026/10/22">','');
  assert.equal(inspectPublicationSemantics(mutated, specimen).filter(issue=>/Scholarly metadata/.test(issue)).length, 2);
});
test('website update cannot silently date a frozen manuscript revision', () => assert.ok(inspectPublicationSemantics(validHtml.replace('"datePublished":"2026-10-22"','"datePublished":"2026-10-22","dateModified":"2026-10-24"'), specimen).some(issue=>/JSON-LD/.test(issue))));
test('arXiv and Journal records belong in publication status, not primary buttons', () => assert.ok(inspectPublicationSemantics(validHtml.replace('class="publication-status"','class="publication-primary"'), specimen).some(issue=>/status line/.test(issue))));
