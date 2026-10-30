# QICLean source slice

Finite-dimensional quantum-channel and GKSL foundations from [LionSR/QICLean](https://github.com/LionSR/QICLean/tree/4d5bcdbe6e92fa64c60d0361cf5472445deba534), commit `4d5bcdbe6e92fa64c60d0361cf5472445deba534`.

The 31 source modules listed in `sources.json` retain their original copyright notices and Apache-2.0 license. This is a source subset, not the complete upstream package. Wolf lecture notes and other non-code materials are excluded.

`compat-v435.patch` records two local instances of Mathlib's finite-dimensional normability theorem required to build against Lean and Mathlib v4.35.0. No mathematical definitions or axioms are added by the patch.

The paper-specific model, Pauli/Bloch identities, and measurement projection are proved separately in `TwoStateQuantumEmbedding`.
