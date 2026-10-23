(() => {
  'use strict';
  const toggle = document.querySelector('[data-nav-toggle]');
  const nav = document.getElementById('main-nav');
  if (toggle && nav) {
    const closeMenu = () => { nav.classList.remove('open'); toggle.setAttribute('aria-expanded', 'false'); };
    toggle.addEventListener('click', () => { const open = nav.classList.toggle('open'); toggle.setAttribute('aria-expanded', String(open)); });
    nav.querySelectorAll('a').forEach(a => a.addEventListener('click', closeMenu));
    document.addEventListener('keydown', e => { if (e.key === 'Escape' && nav.classList.contains('open')) { closeMenu(); toggle.focus(); } });
    document.addEventListener('click', e => { if (!e.target.closest('.site-header')) closeMenu(); });
  }
  document.querySelectorAll('[data-current-year]').forEach(el => { el.textContent = new Date().getFullYear(); });
  if ('IntersectionObserver' in window && nav) {
    const links = [...nav.querySelectorAll('a[href^="#"]')];
    const observer = new IntersectionObserver(entries => { entries.forEach(entry => { if (entry.isIntersecting) { links.forEach(a => a.classList.toggle('current', a.hash === '#' + entry.target.id)); } }); }, {rootMargin:'-10% 0px -65% 0px'});
    document.querySelectorAll('main section[id]').forEach(section => observer.observe(section));
  }
  const list = document.getElementById('publication-list');
  if (!list) return;
  const count = document.getElementById('publication-count');
  const search = document.getElementById('publication-search');
  const clear = document.getElementById('clear-search');
  const empty = document.getElementById('publication-empty');
  const filters = [...document.querySelectorAll('[data-filter]')];
  let papers = [], filter = 'all';
  const escape = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const safeURL = url => { try { const parsed = new URL(url, location.href); if (parsed.protocol === 'file:' && location.protocol === 'file:' && !/^[a-z]+:/i.test(url)) return url; return ['https:','http:'].includes(parsed.protocol) ? parsed.href : '#'; } catch { return '#'; } };
  const normalizeSearch = value => String(value).toLocaleLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g, '').replace(/[‐‑‒–—-]/g, ' ').replace(/\s+/g, ' ').trim();
  function render() {
    const query = normalizeSearch(search.value);
    const selected = papers.filter(p => (filter === 'all' || (filter === 'recent' ? p.year >= 2020 : p.status === filter)) && (!query || normalizeSearch([p.title, p.authors.join(' '), p.venue, p.year, ...p.topics].join(' ')).includes(query)));
    count.textContent = `${selected.length} ${selected.length === 1 ? 'publication' : 'publications'}${selected.length !== papers.length ? ' of ' + papers.length : ''} · newest first`;
    empty.hidden = selected.length !== 0;
    clear.hidden = !query && filter === 'all';
    list.innerHTML = selected.map(p => {
      const coauthors = p.authors.filter(name => name !== 'Murat Akman');
      const primary = p.links.find(l => l.label === 'arXiv') || p.links[0];
      return `<article class="publication-item" id="${escape(p.id)}"><div class="publication-year">${escape(p.year)}${p.status === 'Preprint' ? '<small>Preprint</small>' : ''}</div><div class="publication-content"><h3 class="publication-title">${primary ? `<a href="${escape(safeURL(primary.url))}">${escape(p.title.replace(/\.$/,''))}</a>` : escape(p.title.replace(/\.$/,''))}</h3><p class="publication-authors">${coauthors.length ? 'With ' + escape(coauthors.join(', ')) : 'Murat Akman'}</p><p class="publication-venue">${escape(p.venue)}</p><div class="publication-links">${p.links.map(l => `<a href="${escape(safeURL(l.url))}" aria-label="${escape(l.label)}: ${escape(p.title)}">${escape(l.label)} <span aria-hidden="true">↗</span></a>`).join('')}<button class="abstract-toggle" type="button" aria-expanded="false" aria-controls="abstract-${escape(p.id)}">Abstract <span aria-hidden="true">+</span></button></div><div class="publication-abstract" id="abstract-${escape(p.id)}" hidden>${p.abstract.split(/\n\s*\n/).map(paragraph => `<p>${escape(paragraph)}</p>`).join('')}</div></div></article>`;
    }).join('');
    filters.forEach(button => { const active = button.dataset.filter === filter; button.classList.toggle('active', active); button.setAttribute('aria-pressed', String(active)); });
  }
  list.addEventListener('click', async event => {
    const button = event.target.closest('.abstract-toggle');
    if (!button) return;
    const abstract = document.getElementById(button.getAttribute('aria-controls'));
    const open = button.getAttribute('aria-expanded') !== 'true';
    button.setAttribute('aria-expanded', String(open));
    button.querySelector('span').textContent = open ? '−' : '+';
    abstract.hidden = !open;
    if (open && /\$|\\\[/.test(abstract.textContent)) {
      try { await loadMath(); if (window.MathJax?.typesetPromise) await window.MathJax.typesetPromise([abstract]); } catch { /* The text remains available if the optional maths renderer cannot load. */ }
    }
  });
  let mathPromise;
  function loadMath() {
    if (window.MathJax?.typesetPromise) return Promise.resolve();
    if (!mathPromise) mathPromise = new Promise((resolve,reject) => {
      window.MathJax = { tex:{inlineMath:[['$','$'],['\\(','\\)']],displayMath:[['\\[','\\]'],['$$','$$']],processEscapes:true}, svg:{fontCache:'global'}, startup:{typeset:false} };
      const script = document.createElement('script'); script.src = 'https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-svg.js'; script.async = true;
      script.onload = () => window.MathJax.startup.promise.then(resolve,reject); script.onerror = reject; document.head.appendChild(script);
    });
    return mathPromise;
  }
  filters.forEach(button => button.addEventListener('click', () => { filter = button.dataset.filter; render(); }));
  search.addEventListener('input', render);
  clear.addEventListener('click', () => { filter = 'all'; search.value = ''; render(); search.focus(); });
  if (Array.isArray(window.MURAT_PUBLICATIONS)) {
    papers = window.MURAT_PUBLICATIONS.slice().sort((a,b) => b.year - a.year || Number(b.id.replace(/\D/g,'')) - Number(a.id.replace(/\D/g,'')));
    render();
  } else {
    count.textContent = 'Publication list';
    list.innerHTML = '<p>Please visit the <a class="text-link" href="publication.html">complete publication list ↗</a>.</p>';
  }
})();
