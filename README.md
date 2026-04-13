# Heterogeneous Dynamic Logic

This artifact contains the Isabelle formalization of the paper *Heterogeneous Dynamic Logic: Provability Modulo Program Theories*.
We formalize *dynamic theories* and prove that three dynamic logics are instantiations of this concept.

We provide a [reference](/documentation/Isabelle-Paper-Reference.pdf) which maps concepts from the paper to Isabelle definitions and lemmas.
A more detailed documentation of heterogeneous dynamic logic can be found in the [proof outline](/documentation/outline-hdl.pdf).
A documentation of the proof that differential dynamic logic is an instantiation of a dynamic theory can be found [here](/documentation/outline-diff-dl.pdf).

## Dependencies
This formalization was built with **Isabelle 2025** (March 2025 release) available [here](https://isabelle.in.tum.de/website-Isabelle2025/index.html)

Additionally, we require the following dependencies:
- TeXLive (for building the proof outlines via Isabelle)
- Z3

The proof that differential dynamic logic is an instantiation of a dynamic theory is based on the AFP differential dynamic logic formalization by Rose Bohrer.
The proof was built with the Isabelle 2025 release of the AFP available [here](https://foss.heptapod.net/isa-afp/afp-devel/-/archive/Isabelle2025/afp-devel-Isabelle2025.zip?ref_type=tags)

## Getting Started

- Download and install Isabelle (use [this link](https://isabelle.in.tum.de/website-Isabelle2025/index.html) or archive.org mirrors below)
- Download and install TeXLive and Z3  
  For Debian-based systems this can be achieved via: `sudo apt install texlive z3`
- *To build differential dynamic logic instantiation:* Download [2025 Version of the AFP](https://foss.heptapod.net/isa-afp/afp-devel/-/archive/Isabelle2025/afp-devel-Isabelle2025.zip?ref_type=tags) (alternatively see archive.org mirror below)
- *If necessary:* Adapt the paths for the isabelle binary (typically `[Isabelle folder]/bin/isabelle`) and the AFP (`[AFP folder]/thys`) in the `build.sh` script:  
  ```
    export ISABELLE="[Isabelle path here]"
    export ISABELLE_AFP_THYS="[AFP path here]"
    ```
- **Building the formalization:** Run `build.sh`  
  This command will run for a while (up to 35 minutes) and should eventually report that, both, the heterogeneous dynamic logic formalization and the formalization of the differential dynamic logic instantiation have been built.
- **Inspecting/Using the formalization:** To inspect, extend or use the formalization in Isabelle, you can open it at as follows in its editor `jedit`: `[Path to Isabelle Binary] jedit -d . DynamicLogicCore.thy`


## Reproducibility
To ensure reproducibility beyond the lifespan of linked servers, we also refer to a mirror on archive.org:
- Isabelle 2025:
    - Linux (Intel): [zip via archive.org (slower)](https://web.archive.org/web/20250330090403/https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_linux.tar.gz)
    - Linux (ARM): [zip via archive.org (slower)](https://web.archive.org/web/20260317202834/https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_linux_arm.tar.gz)
    - Windows: [zip via archive.org (slower)](https://web.archive.org/web/20260317202724/https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025.exe)
    - Apple: [zip via archive.org (slower)](https://web.archive.org/web/20260317202744/https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_macos.tar.gz)
- AFP: [zip available for download via archive.org (slower)](https://web.archive.org/web/20260317165431/https://foss.heptapod.net/isa-afp/afp-devel/-/archive/Isabelle2025/afp-devel-Isabelle2025.zip?ref_type=tags)