/** Keep intact tables scrollable without filling the tab order with tables that fit. */
export function initializeTableLayout() {
  const wrappers = [...document.querySelectorAll<HTMLElement>("[data-table-scroll]")];
  if (!wrappers.length) return;
  const hints = new Map<HTMLElement, HTMLParagraphElement>();
  for (const wrapper of wrappers) {
    if (!wrapper.previousElementSibling?.classList.contains("table-instruction")) {
      const hint = document.createElement("p");
      hint.className = "table-scroll-hint";
      hint.textContent = "Scroll horizontally for all columns. Keyboard: focus the table area, then use the left and right arrow keys.";
      hint.hidden = true;
      wrapper.before(hint);
      hints.set(wrapper, hint);
    }
  }
  const update = () => {
    for (const wrapper of wrappers) {
      const visible = wrapper.getClientRects().length > 0;
      const overflowing = visible && wrapper.scrollWidth > wrapper.clientWidth + 1;
      wrapper.dataset.tableOverflow = String(overflowing);
      const hint = hints.get(wrapper);
      if (hint) hint.hidden = !overflowing;
      // Preserve intentional, author-supplied accessibility (e.g. nutrient
      // contribution tables). Only manage attributes added by the shared build.
      if (wrapper.dataset.tableEnhanced !== "auto") continue;
      if (overflowing) {
        wrapper.tabIndex = 0;
        wrapper.setAttribute("role", "region");
        wrapper.setAttribute("aria-label", `${wrapper.dataset.tableLabel || "Data table"}; scroll horizontally`);
      } else {
        wrapper.removeAttribute("tabindex");
        wrapper.removeAttribute("role");
        wrapper.removeAttribute("aria-label");
      }
    }
  };
  let scheduled = false;
  const schedule = () => {
    if (scheduled) return;
    scheduled = true;
    requestAnimationFrame(() => { scheduled = false; update(); });
  };
  const observer = new ResizeObserver(schedule);
  for (const wrapper of wrappers) {
    observer.observe(wrapper);
    const table = wrapper.querySelector("table");
    if (table) observer.observe(table);
  }
  document.addEventListener("toggle", schedule, true);
  window.addEventListener("resize", schedule, { passive: true });
  document.fonts.ready.then(schedule);
  update();
}
