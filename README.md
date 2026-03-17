# Heterogeneous Dynamic Logic

This artifact contains the Isabelle formalization of the paper *Heterogeneous Dynamic Logic: Provability Modulo Program Theories*.
We formalize *dynamic theories* and prove that three dynamic logics are instantiations of this concept.

We provide a [reference](/documentation/Isabelle-Paper-Reference.pdf) which maps concepts from the paper to Isabelle definitions and lemmas.
A more detailed documentation of heterogeneous dynamic logic can be found in the [proof outline](/documentation/outline-hdl.pdf).
A documentation of the proof that differential dynamic logic is an instantiation of a dynamic theory can be found [here](/documentation/outline-diff-dl.pdf).

## Dependencies
This formalization was built with **Isabelle 2025** (March 2025 release) available [here](https://isabelle.in.tum.de/website-Isabelle2025/index.html)

The proof that differential dynamic logic is an instantiation of a dynamic theory is based on the AFP differential dynamic logic formalization by Rose Bohrer.
The proof was built with the Isabelle 2025 release of the AFP available [here](https://foss.heptapod.net/isa-afp/afp-devel/-/archive/Isabelle2025/afp-devel-Isabelle2025.zip?ref_type=tags)

## Building the Formalization

To compile the theories in Isabelle,
update the directory pointers to Isabelle and the AFP's `./thys/` directory in `build.sh` and then run it.

## Reproducibility
To ensure reproducibility beyond the lifespan of linked servers, we also refer to a mirror on archive.org:
- Isabelle 2025:
    - Linux (Intel): [zip via archive.org (slower)](https://web.archive.org/web/20250330090403/https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_linux.tar.gz)
    - Linux (ARM): [zip via archive.org (slower)](https://web.archive.org/web/20260317202834/https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_linux_arm.tar.gz)
    - Windows: [zip via archive.org (slower)](https://web.archive.org/web/20260317202724/https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025.exe)
    - Apple: [zip via archive.org (slower)](https://web.archive.org/web/20260317202744/https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_macos.tar.gz)
- AFP: [zip available for download via archive.org (slower)](https://web.archive.org/web/20260317165431/https://foss.heptapod.net/isa-afp/afp-devel/-/archive/Isabelle2025/afp-devel-Isabelle2025.zip?ref_type=tags)