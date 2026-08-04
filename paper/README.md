# Architecture paper

This directory vendors the LLNCS paper template from
[`qianchen92/submissionTemp`](https://github.com/qianchen92/submissionTemp) at
commit `abfbab78fbefcb8e99fa044a24806622dfb7ca6b` (2026-01-26).

The upstream archive stores `cryptobib/` as ordinary files even though its
root `.gitmodules` describes that path as a submodule. The nested
`.gitmodules` file is intentionally omitted here: this paper keeps the exact
vendored bibliography needed for a self-contained build and does not alter the
parent repository's submodule configuration.

Build from this directory with:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Clean generated files with `latexmk -C`. The stable rendered artifact is also
copied to `../output/pdf/crypto-infrastructure-architecture.pdf` after visual
inspection.
