# Two-state quantum embedding

**Tingyu Zhang**

[English paper](paper/manuscript.pdf) · [中文论文](paper/manuscript_zh.pdf) · [中文说明](README.zh-CN.md) · [Theorem-to-code map](theorem-map.md)

This repository accompanies a research manuscript on fixed-basis probability tables produced by time-independent qubit GKSL generators. The main results determine the exact tangent cone at the swap endpoint and prove that the true lower boundary has a real-analytic extension near that endpoint. The Lean development starts from arbitrary finite collections of jump operators and the original closure of attainable probability tables.

The paper also develops the exact drift geometry and bias intervals, a logarithmic reset construction, and the square-root channel layer. Its statements are matched to checked Lean declarations in [theorem-map.md](theorem-map.md). The full middle boundary remains open.

## Contents

- `paper/`: complete English and Chinese papers, in PDF and LaTeX.
- `lean/`: Lean sources, pinned dependencies, and the vendored QICLean foundations.
- `verification/`: the main-theorem axiom audit and build evidence.
- [Research status](research-status.md): the scope of this release and work retained for continuation.

## Check the proofs

Install [elan](https://github.com/leanprover/elan). Set `LEAN_NUM_THREADS=2` for a memory-bounded build (`$env:LEAN_NUM_THREADS='2'` in PowerShell), then run:

```sh
cd lean
lake exe cache get
lake build TwoStateQuantumEmbedding QICLean
lake env lean ../verification/PublicationAudit.lean
```

The toolchain is Lean `v4.35.0`; `lake-manifest.json` fixes the Mathlib revision. The release audit permits only `propext`, `Classical.choice`, and `Quot.sound`. Source compilation and the axiom audit complement the mathematical reading of the theorem statements; the correspondence table specifies precisely what the paper claims.

## Build the papers

With a LaTeX distribution containing `ctex`, Fandol fonts, and the usual AMS packages:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex
latexmk -xelatex -interaction=nonstopmode -halt-on-error manuscript_zh.tex
```

## Attribution

The manuscript and project-specific proofs are by Tingyu Zhang. Third-party QICLean sources retain their original authorship and Apache-2.0 license; see [provenance](lean/vendor/QICLean/README.md). Copyright and licensing information is in [NOTICE.md](NOTICE.md).
