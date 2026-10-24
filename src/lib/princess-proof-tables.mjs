/** Restore the authored two-level headings of the preserved cube comparison.
 * Pandoc exports the TeX multicolumn headings as td. This exact table has two
 * named board groups, each with Daily budget / Minimum days columns. No labels
 * or mathematical data are inferred or changed, including in the frozen source.
 */
export function restorePrincessProofTableHeaders(html) {
  return html.replace(/<table\b[^>]*>[\s\S]*?<\/table>/g, (table) => {
    if (!table.includes('4\\times4\\times4') || !table.includes('3\\times4\\times4') ||
        !table.includes('Daily budget') || !table.includes('Minimum days') || table.includes('<th')) return table;
    let row = 0;
    return table.replace('<table>', '<table><colgroup span="2"></colgroup><colgroup span="2"></colgroup>')
      .replace(/<tr\b[^>]*>[\s\S]*?<\/tr>/g, (markup) => {
        const index = row++;
        if (index > 1) return markup;
        const scope = index === 0 ? 'colgroup' : 'col';
        return markup.replace(/<td\b/g, `<th scope="${scope}"`).replaceAll('</td>', '</th>');
      });
  });
}
