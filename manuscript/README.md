# Manuscript snapshot

`manuscript.pdf` is the exact source snapshot used for the 1.1.0
formalization release. It was rebuilt from the author's current LaTeX source on
2026-08-13 and contains 74 pages.

Provenance: the PDF was built from the file now bundled as `manuscript.tex` in
the [`BennyAvelin/NNCutoff`](https://github.com/BennyAvelin/NNCutoff) source
repository at commit `527fc7f26bcfe863eebb44aad4dd9107ddd5fad1`. The
self-contained LaTeX inputs from that commit are bundled in [`source/`](source/)
because the commit had not yet been pushed to that separate repository when
this release was prepared. The bundle includes the `.bbl` generated from that
commit's `refs.bib` and the seven used figures. From that directory, the
snapshot can be rebuilt without BibTeX by running
`pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex`
three times.

SHA-256:

```text
873d155bb25921c97adc2d8b1764c54dc3184a6495c17202558ad1f7d841182a  manuscript.pdf
```

This fixed copy and its build inputs are included so the manuscript-to-Lean
correspondence can be reviewed even before an arXiv version is available. When
an arXiv version is posted, its identifier will be added without changing the
provenance of this release snapshot.

Copyright © 2026 Benny Avelin. All rights reserved. The manuscript PDF and
the files under `source/` are not covered by the repository's Apache License 2.0.
