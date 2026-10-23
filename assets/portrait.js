/* After a quiet moment, the portrait becomes a domain of level curves. */
(() => {
  const art = document.querySelector('.portrait-art');
  const button = art?.querySelector('.portrait-reveal');
  if (!button) return;

  const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)');
  const image = button.querySelector('img');
  const silhouette = button.querySelector('.portrait-silhouette');
  const idleDelay = 30000;
  let timer;
  let hovering = false;
  let keyboardFocused = false;
  let ready = false;

  const clearTimer = () => window.clearTimeout(timer);
  const reveal = () => {
    clearTimer();
    art.classList.remove('is-silhouette');
    button.setAttribute('aria-label', 'Show portrait');
  };
  const startTimer = () => {
    clearTimer();
    if (!ready || reducedMotion.matches || hovering || keyboardFocused) return;
    timer = window.setTimeout(() => {
      art.classList.add('is-silhouette');
      button.setAttribute('aria-label', 'Reveal portrait');
    }, idleDelay);
  };

  button.addEventListener('pointerenter', event => {
    if (event.pointerType !== 'mouse') return;
    hovering = true;
    reveal();
  });
  button.addEventListener('pointerleave', event => {
    if (event.pointerType !== 'mouse') return;
    hovering = false;
    startTimer();
  });
  button.addEventListener('focus', () => {
    keyboardFocused = button.matches(':focus-visible');
    if (keyboardFocused) reveal();
  });
  button.addEventListener('blur', () => {
    keyboardFocused = false;
    startTimer();
  });
  button.addEventListener('click', () => {
    reveal();
    startTimer();
  });
  reducedMotion.addEventListener('change', () => {
    reveal();
    startTimer();
  });
  window.addEventListener('pagehide', clearTimer);
  window.addEventListener('pageshow', event => {
    if (!event.persisted) return;
    hovering = false;
    keyboardFocused = button.matches(':focus-visible');
    reveal();
    startTimer();
  });

  // Keep the untouched photo if either layer cannot load.
  Promise.all([image.decode(), silhouette.decode()]).then(() => {
    ready = true;
    button.disabled = false;
    startTimer();
  }).catch(() => {});
})();
