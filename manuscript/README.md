# Manuscript snapshot

`manuscript.pdf` is the current manuscript snapshot tracked alongside the
formalization. It was rebuilt from the author's LaTeX source on 2026-08-16 and
contains 72 pages.

Provenance: the PDF was built from the file now bundled as `manuscript.tex` in
the [`BennyAvelin/NNCutoff`](https://github.com/BennyAvelin/NNCutoff) source
repository at commit `d35ee3ab23d72cca6311f84695728caad83266ec`. The
self-contained LaTeX inputs from that commit are bundled in [`source/`](source/).
The bundle includes the `.bbl` generated from that commit's `refs.bib` and the
seven used figures. From that directory, the
snapshot can be rebuilt without BibTeX by running
`pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex`
three times.

SHA-256:

```text
585b75efde1438a68d9ee9abbc98f8ad83e7805a6b54199b14bf9cfdcfb3bac9  manuscript.pdf
```

This copy and its build inputs are included so the manuscript-to-Lean
correspondence can be reviewed even before an arXiv version is available. The
fixed snapshot shipped with formalization release 1.1.0 remains available at
tag `v1.1`.

Copyright © 2026 Benny Avelin. All rights reserved. The manuscript PDF and
the files under `source/` are not covered by the repository's Apache License 2.0.
