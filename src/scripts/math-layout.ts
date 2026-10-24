/** Preserve intact math at small widths without shrinking it or moving the page. */
export function initializeMathLayout() {
  const displays = [...document.querySelectorAll<HTMLElement>(".katex-display")];
  const inline = [...document.querySelectorAll<HTMLElement>(".katex")]
    .filter((element) => !element.closest(".katex-display"));
  if (!displays.length && !inline.length) return;
  const originalAttributes = new Map<HTMLElement, (string | null)[]>();
  const scrollAttributes = ["tabindex", "role", "aria-label"];
  const update = (element: HTMLElement) => {
    if (element.scrollWidth > element.clientWidth + 1) {
      if (!originalAttributes.has(element)) {
        originalAttributes.set(element, scrollAttributes.map((name) => element.getAttribute(name)));
      }
      element.tabIndex = 0;
      element.setAttribute("role", "region");
      const label = originalAttributes.get(element)?.[2];
      element.setAttribute("aria-label", label ? `${label}; scroll horizontally` : "Mathematical expression; scroll horizontally");
    } else if (originalAttributes.has(element)) {
      originalAttributes.get(element)!.forEach((value, index) => {
        if (value === null) element.removeAttribute(scrollAttributes[index]);
        else element.setAttribute(scrollAttributes[index], value);
      });
      originalAttributes.delete(element);
    }
  };
  const updateAll = () => {
    for (const element of inline) {
      // Let normal KaTeX relation/operator breaks work first. Only an atom still
      // wider than its text column needs an accessible, full-width scroll box.
      const scrollLeft = element.scrollLeft;
      element.classList.remove("math-inline-overflow");
      const column = element.closest<HTMLElement>("p, li, td, th, figcaption, h1, h2, h3, h4, h5, h6, article");
      if (!column || element.closest(".tablewrap")) continue;
      const style = getComputedStyle(column);
      const available = column.clientWidth - Number.parseFloat(style.paddingLeft) - Number.parseFloat(style.paddingRight);
      if (element.getBoundingClientRect().width > available + 1) element.classList.add("math-inline-overflow");
      update(element);
      if (element.classList.contains("math-inline-overflow")) element.scrollLeft = scrollLeft;
    }
    displays.forEach(update);
  };
  let scheduled = false;
  const schedule = () => {
    if (scheduled) return;
    scheduled = true;
    requestAnimationFrame(() => { scheduled = false; updateAll(); });
  };
  const observer = new ResizeObserver(schedule);
  observer.observe(document.querySelector("article") ?? document.body);
  updateAll();
  document.fonts.ready.then(schedule);
}
