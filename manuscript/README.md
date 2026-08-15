# Manuscript snapshot

`manuscript.pdf` is the current manuscript snapshot tracked alongside the
formalization. It was rebuilt from the author's LaTeX source on 2026-08-15 and
contains 71 pages.

Provenance: the PDF was built from the file now bundled as `manuscript.tex` in
the [`BennyAvelin/NNCutoff`](https://github.com/BennyAvelin/NNCutoff) source
repository at commit `1bc4a8a29e0fe2bdd27f06ca2e48b0ca2b94c844`. The
self-contained LaTeX inputs from that commit are bundled in [`source/`](source/).
The bundle includes the `.bbl` generated from that commit's `refs.bib` and the
seven used figures. From that directory, the
snapshot can be rebuilt without BibTeX by running
`pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex`
three times.

SHA-256:

```text
f7bb06730684105c30307ae8adf3c27fe0a905b7ddb5b1067e033911c6c9e766  manuscript.pdf
```

This copy and its build inputs are included so the manuscript-to-Lean
correspondence can be reviewed even before an arXiv version is available. The
fixed snapshot shipped with formalization release 1.1.0 remains available at
tag `v1.1`.

Copyright © 2026 Benny Avelin. All rights reserved. The manuscript PDF and
the files under `source/` are not covered by the repository's Apache License 2.0.
