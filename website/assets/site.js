'use strict';
// Only progressive enhancement: every page and formula is already in the HTML.
document.querySelectorAll('[data-search]').forEach(input => {
  const items = [...document.querySelectorAll(input.dataset.search)];
  const count = document.getElementById(input.dataset.count);
  input.value = new URLSearchParams(location.search).get('q') || '';
  function update() {
    const words = input.value.toLocaleLowerCase().trim().split(/\s+/).filter(Boolean);
    let targetId = '';
    try { targetId = decodeURIComponent(location.hash.slice(1)); } catch (_) { /* Invalid fragment. */ }
    let visible = 0;
    items.forEach(item => {
      const match = words.every(word => item.textContent.toLocaleLowerCase().includes(word))
        || (targetId && item.id === targetId);
      item.hidden = !match;
      if (match) visible += 1;
    });
    if (count) count.textContent = input.dataset.countTemplate
      .replace('{visible}', visible).replace('{total}', items.length);
  }
  input.addEventListener('input', () => {
    update();
    // file:// may disallow replaceState. Language links still read the input directly.
    try {
      const url = new URL(location.href);
      if (input.value) url.searchParams.set('q', input.value);
      else url.searchParams.delete('q');
      history.replaceState(null, '', url.href);
    } catch (_) { /* No persistence is needed to filter or switch languages. */ }
  });
  window.addEventListener('hashchange', () => {
    update();
    try {
      document.getElementById(decodeURIComponent(location.hash.slice(1)))?.scrollIntoView();
    } catch (_) { /* Invalid fragment. */ }
  });
  update();
});

document.querySelectorAll('[data-language-switch]').forEach(link => {
  function preserveContext() {
    const target = new URL(link.getAttribute('href'), location.href);
    target.search = location.search;
    target.hash = location.hash;
    const input = document.querySelector('[data-search]');
    if (input) {
      if (input.value) target.searchParams.set('q', input.value);
      else target.searchParams.delete('q');
    }
    link.href = target.href;
  }
  link.addEventListener('click', preserveContext);
  link.addEventListener('contextmenu', preserveContext);
  link.addEventListener('focus', preserveContext);
});
