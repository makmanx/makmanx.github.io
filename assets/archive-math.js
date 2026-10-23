/* Load mathematical typesetting only when an archive abstract is opened. */
(() => {
  let ready;
  document.addEventListener('toggle', event => {
    const details = event.target;
    if (!details.matches?.('.publication-content > details') || !details.open) return;
    const abstract = details.querySelector('.publication-abstract');
    if (!abstract || !/\$|\\\[/.test(abstract.textContent)) return;
    if (!ready) ready = new Promise((resolve, reject) => {
      window.MathJax = {tex:{inlineMath:[['$','$'],['\\(','\\)']],displayMath:[['\\[','\\]'],['$$','$$']],processEscapes:true},svg:{fontCache:'global'},startup:{typeset:false}};
      const script = document.createElement('script');
      script.src = 'https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-svg.js';
      script.async = true;
      script.onload = () => window.MathJax.startup.promise.then(resolve, reject);
      script.onerror = reject;
      document.head.appendChild(script);
    });
    ready.then(() => window.MathJax.typesetPromise([abstract])).catch(() => {});
  }, true);
})();
