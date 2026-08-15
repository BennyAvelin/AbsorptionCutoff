# Manuscript snapshot

`manuscript.pdf` is the current manuscript snapshot tracked alongside the
formalization. It was rebuilt from the author's LaTeX source on 2026-08-15 and
contains 72 pages.

Provenance: the PDF was built from the file now bundled as `manuscript.tex` in
the [`BennyAvelin/NNCutoff`](https://github.com/BennyAvelin/NNCutoff) source
repository at commit `9795eec6a32dff9ca60a4fbcc5850cfb79fc0338`. The
self-contained LaTeX inputs from that commit are bundled in [`source/`](source/).
The bundle includes the `.bbl` generated from that commit's `refs.bib` and the
seven used figures. From that directory, the
snapshot can be rebuilt without BibTeX by running
`pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex`
three times.

SHA-256:

```text
8b830dc4e88daa8c363dd33779debf881036f8808866ff8149d5f557531afe3f  manuscript.pdf
```

This copy and its build inputs are included so the manuscript-to-Lean
correspondence can be reviewed even before an arXiv version is available. The
fixed snapshot shipped with formalization release 1.1.0 remains available at
tag `v1.1`.

Copyright © 2026 Benny Avelin. All rights reserved. The manuscript PDF and
the files under `source/` are not covered by the repository's Apache License 2.0.
