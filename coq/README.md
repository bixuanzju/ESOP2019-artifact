
# Coq Formalization Artifact

The artifact contains the Coq formalization of Fi+, as described in the paper
"Distributive Disjoint Polymorphism for Compositional Programming". We document
in detail how to build and compile the Coq proofs, as well as the proof
structure and organization.



## Building Instructions

Our Coq proofs are verified in **Coq 8.8.2**. We rely on two Coq libraries:
[`metalib`](https://github.com/plclub/metalib) for the locally nameless
representation in our proofs; and
[`coq-equations`](https://github.com/mattam82/Coq-Equations) for defining
logical relations using pattern matching.



### Prerequisites

1. Install Coq 8.8.2. The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.8.2). Choose a suitable installer
   according to your platform.

2. Make sure `Coq` is installed (type `coqc` in the terminal, if you see "command
   not found" this means you have not properly installed Coq), then install `metalib`:
   1. Open terminal
   2. `git clone https://github.com/plclub/metalib`
   3. `cd metalib/Metalib`
   4. `make install`

3. Install `coq-equations.1.0+8.8`, refer to [here](https://github.com/mattam82/Coq-Equations#installation).
   1. `opam repo add coq-released https://coq.inria.fr/opam/released`
   2. `opam install coq-equations.1.0+8.8`


### Build and Compile the Proofs

1. Type `make` in the terminal to build and compile the proofs.

2. You should see something like the following (suppose `>` is the prompt):
   ```sh
   coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
   COQC Syntax_ott.v
   COQC TypeSystems.v
   COQC LibTactics.v
   COQC SystemF_inf.v
   COQC Fii_inf.v
   COQC Infrastructure.v
   COQC Algorithm.v
   COQC Assumed.v
   COQC SourceProperty.v
   COQC Disjoint.v
   COQC TargetProperty.v
   COQC LR.v
   COQC Compatibility.v
   COQC Coherence.v
   COQC SoundComplete.v
   ```

## Proof Structure

- `Syntax_ott.v` contains the locally nameless definitions of the calculi.
- `TypeSystems.v` contains the type systems of the calculi.
- `SourceProperty.v` contains some properties of the source language.
- `TargetProperty.v` contains some properties of the target language.
- `LR.v` contains definition of the logical relation
- `Disjoint.v` contains some properties of the disjointness relation.
- `Compatibility.v`contains the compatibility lemmas.
- `Coherence.v` contains the proofs of the coherence property.
- `Algorithm.v` contains the definition of the algorithmic subtyping.
- `SoundComplete.v` contains the soundness and completeness proofs of the algorithmic subtyping.
- `Fii_inf.v` contains auxiliary lemmas of the source language.
- `SystemF_inf.v` contains auxiliary lemmas of the target language.
- `Infrastructure.v` contains some auxiliary lemmas.
- `Assumed.v` contains axioms (e.g., strong normalization) that are well-known in the literature.
