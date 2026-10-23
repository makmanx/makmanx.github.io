/* Let the mathematics show through the portrait after 30 quiet seconds. */
(() => {
  const art = document.querySelector('.portrait-art');
  const button = art?.querySelector('.portrait-reveal');
  if (!button) return;

  const photo = art.querySelector('img');
  const background = art.querySelector('.portrait-math-layer');
  const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)');
  const mask = new Image();
  mask.src = new URL('assets/portrait-person-mask.svg', document.baseURI).href;
  const idleDelay = 30000;
  let timer;
  let ready = false;
  let keyboardFocused = false;

  const clearTimer = () => window.clearTimeout(timer);
  const showPortrait = () => {
    clearTimer();
    art.classList.remove('math-revealed');
  };
  const startTimer = () => {
    clearTimer();
    if (!ready || reducedMotion.matches || keyboardFocused) return;
    timer = window.setTimeout(() => art.classList.add('math-revealed'), idleDelay);
  };
  const revealAndRestart = () => {
    showPortrait();
    startTimer();
  };

  button.addEventListener('pointerenter', event => {
    if (event.pointerType === 'mouse') revealAndRestart();
  });
  button.addEventListener('pointermove', event => {
    if (event.pointerType === 'mouse' && art.classList.contains('math-revealed')) {
      revealAndRestart();
    }
  });
  button.addEventListener('focus', () => {
    keyboardFocused = button.matches(':focus-visible');
    if (keyboardFocused) showPortrait();
  });
  button.addEventListener('blur', () => {
    keyboardFocused = false;
    startTimer();
  });
  button.addEventListener('click', revealAndRestart);

  const updateMotionPreference = () => {
    showPortrait();
    button.hidden = !ready || reducedMotion.matches;
    startTimer();
  };
  reducedMotion.addEventListener('change', updateMotionPreference);
  window.addEventListener('pagehide', clearTimer);
  window.addEventListener('pageshow', event => {
    if (!event.persisted) return;
    keyboardFocused = button.matches(':focus-visible');
    revealAndRestart();
  });

  // Keep the original photo if a layer or its mask cannot load.
  Promise.all([photo.decode(), background.decode(), mask.decode()]).then(() => {
    ready = true;
    updateMotionPreference();
  }).catch(() => {});
})();
