document.querySelectorAll('[data-current-year]').forEach((node) => {
  node.textContent = String(new Date().getFullYear());
});

const formatMonth = (published) => {
  const date = new Date(`${published.slice(0, 10)}T00:00:00Z`);
  return new Intl.DateTimeFormat('en', {
    month: 'long',
    year: 'numeric',
    timeZone: 'UTC',
  }).format(date);
};

const initializePaperNavigation = async () => {
  const navigation = document.querySelector('[data-paper-navigation]');
  if (!navigation) {
    return;
  }

  const siteRoot = document.body.dataset.siteRoot || './';
  const currentSlug = document.body.dataset.paperSlug || '';

  try {
    const response = await fetch(new URL(`${siteRoot}data/papers.json`, document.baseURI), {
      cache: 'no-store',
    });
    if (!response.ok) {
      throw new Error(`Paper index request failed with HTTP ${response.status}.`);
    }

    const payload = await response.json();
    const fragment = document.createDocumentFragment();

    payload.papers.forEach((paper) => {
      const link = document.createElement('a');
      const time = document.createElement('time');
      const label = document.createElement('span');

      link.href = new URL(`${siteRoot}${paper.path}`, document.baseURI);
      time.dateTime = paper.published.slice(0, 7);
      time.textContent = formatMonth(paper.published);
      label.textContent = paper.label;

      if (paper.slug === currentSlug) {
        link.classList.add('active');
        link.setAttribute('aria-current', 'page');
      }

      link.append(time, label);
      fragment.append(link);
    });

    navigation.replaceChildren(fragment);
  } catch (error) {
    console.warn('Automatic paper navigation is unavailable.', error);
  }
};

initializePaperNavigation();
