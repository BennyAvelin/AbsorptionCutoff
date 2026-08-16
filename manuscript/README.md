# Manuscript snapshot

`manuscript.pdf` is the current manuscript snapshot tracked alongside the
formalization. It was rebuilt from the author's LaTeX source on 2026-08-16 and
contains 72 pages.

Provenance: the PDF was built from the LaTeX file bundled as
[`source/manuscript.tex`](source/manuscript.tex). The self-contained inputs are
bundled in [`source/`](source/), including the generated `.bbl` and the seven
used figures. From that directory, the
snapshot can be rebuilt without BibTeX by running
`pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex`
three times.

SHA-256:

```text
b763e4f51ec5f64c13ad7b59a1105dc0fdf5e8260a5b064b2cbb0f02ac312972  manuscript.pdf
```

This copy and its build inputs are included so the manuscript-to-Lean
correspondence can be reviewed even before an arXiv version is available. The
fixed snapshot shipped with formalization release 1.1.0 remains available at
tag `v1.1`.

Copyright © 2026 Benny Avelin. All rights reserved. The manuscript PDF and
the files under `source/` are not covered by the repository's Apache License 2.0.
