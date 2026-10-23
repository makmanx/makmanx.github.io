# Murat Akman — academic website

A responsive, buildless website prepared for the existing `makmanx.github.io` GitHub Pages site.

## Preview

Open `index.html` in a browser. For a local server, run `python3 -m http.server 8000` from this folder, then visit `http://localhost:8000`.

The site works without a package manager or a build step. The main portrait is a compressed WebP; the original PNG is also in `assets/`. Mathematical typesetting inside abstracts loads MathJax from jsDelivr when needed. Archived course pages use the compatible MathJax 2.7.9 loader from cdnjs. Inline formula SVGs retain their inline layout; display equations can scroll inside an abstract. The main layout, navigation, search and filters work without external libraries.

## Edit

- `index.html`: homepage content, research, teaching overview, supervision and contact details.
- `assets/style.css`: shared typography, responsive layout, maths and publication styling.
- `assets/portrait-landing.css`: portrait entrance, radial links and responsive header.
- `assets/events.css`: Essex event gallery and upcoming programme.
- `assets/app.js`: publication search, filters, abstracts and mobile navigation.
- `assets/publications.js`: editable publication array used by the homepage. Keep `assets/publications.json` in sync if updating the source data.
- `publication.html`: static publication list with accessible abstract disclosures; keep this in sync with publication updates.
- `teaching.html`, `semcon.html`, `travel.html`, `ro.html`, `gam.html`: teaching, conferences, talks, research opportunities and grant resources.
- `rpde.html`, `rpdecv.html`: preserved conference programmes and slides.
- `assets/academic.css`: supporting-page layout.

Original course folders, CV and slide PDFs are retained. The current teaching entry links to the 2026/27 module catalogue; earlier courses and talks are selected archives. The upcoming 2027 Newton Institute programme and the Essex series history from 2022 are included. Historical talks are labelled as archives; funding links are resources, rather than claims of funded vacancies. Two historical UConn talk PDFs (`BSE.pdf` and `HE.pdf`) were absent in the supplied files and original local copy; their unavailable links are marked in that archived course page.

## GitHub Pages

Copy this folder's contents to the root of the existing GitHub Pages repository. Keep `.nojekyll` so the files are served directly. The repository contains static files and needs no build step. GitHub Pages publishes the site after changes are pushed to its publishing branch.

The obsolete site backup, unused original photos and retired Jekyll configuration are excluded from publication. Legacy redirect pages and all linked course materials, papers and slides are retained. `.gitignore` prevents local originals and machine metadata being added again.

No analytics, trackers, forms or backend services are included.

## Content verified in October 2026

- Director of Research: https://www.essex.ac.uk/departments/mathematics-statistics-and-actuarial-science/research
- Newton Institute programme (6 January–30 April 2027, co-organiser): https://www.newton.ac.uk/event/fha/
- Autumn 2026 Real Analysis: https://www1.essex.ac.uk/modules/default.aspx?coursecode=MA203&year=26
- First PDEs @ Essex meeting (4–5 July 2022): https://sites.google.com/essex.ac.uk/pdes-essex/
- Latest preprints: https://arxiv.org/abs/2610.28421 and https://arxiv.org/abs/2603.03061 (September 2026 abstract).
