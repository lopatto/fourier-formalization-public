# Binary Walsh sparse kernels and necessary sampling

Lean 4 formalization associated with Jarosław Błasiok, Patrick Lopatto, Kyle Luh,
Jake Marcinek and Shravas Rao, *An Improved Lower Bound for Sparse Reconstruction
from Subsampled Walsh Matrices*, [arXiv:1903.12135v3](https://arxiv.org/abs/1903.12135v3),
[Discrete Analysis 2023:3](https://doi.org/10.19086/da.74802).

The exact statements follow a local manuscript with explicit finite constants
and error bounds. Its text is not included. These finite refinements and the
inclusive Grassmann endpoints are distinguished from the public paper’s
presentation in `formalization.yaml`.

## Advertised statements

Write `N = 2^n`, `K = 2^k`, with `n ≥ 256`, `k ≤ n` and
`min(k,n-k) ≥ 12 log₂ n`. Each row is included independently with probability
`ρ`; `q = E|Q|` is the actual expected row count. Set `c₀ = ln(2)/8`,
`T = c₀ K log₂ K log₂(N/K)`, and fix `0 < δ < 1` for RIP. Here `X` counts
dimension-`k` subspaces whose annihilators are missed.
`Challenge.lean` gives the complete definitions and hypotheses. The six
same-named declarations listed in `comparator.json` cover:

- `Paper.finiteKernel`: under `0 ≤ ρ ≤ c₀(K/N)k(n-k)`,
  `P(X=0) ≤ B(n,k) ≤ 1/n`, with the same missed subspace's normalized indicator
  a nonzero `K`-sparse kernel vector.
- `Paper.uniformKernel`: the sparse-kernel probability tends to one uniformly
  in admissible sparsity and inclusion probability.
- `Paper.finiteRecovery`: if `q ≤ T`, each recovery/RIP success probability is
  at most `1/n`; if either is greater than `1/n`, then `q > T`.
- `Paper.necessarySampling`: the corresponding lower bound along arbitrary
  admissible dimension sequences tending to infinity when success is eventually
  bounded away from zero, for fixed `0 < δ < 1`.
- `Paper.boundedOrthonormalExample`: the Walsh family has orthonormal columns,
  entry bound `B = 1`, and the same necessary sampling rate.
- `Paper.finiteDecoderComplex`: the finite necessary condition applies to every
  exact uniform decoder and to complex RIP. One scalar is chosen per sampled
  operator before quantifying over signals.

All principal conclusions in this proved binary dyadic scope are included.
Prime-field and quoted introductory results are not advertised. The fixed-ratio
`Ω(K log²N)` interpretation is an algebraic specialization; no separate
arbitrary-`K` or real-`α` rounding theorem is claimed.

## Build and verification

Use the pinned `lean-toolchain` and `lake-manifest.json`. Matching Mathlib artifacts
can be fetched with Mathlib's `lake exe cache get`; keep all caches untracked.

```sh
lake build
lake build Challenge
lake build Solution
lake build StatementChecks
```

`Solution` and `StatementChecks` do not import `Challenge`. Challenge's six
statement holes are deliberate; no admission enters the proof/check closure.
Only `propext`, `Quot.sound` and `Classical.choice` are permitted.

Clean-package checks:

- **PASSED:** full and separate module builds, StatementChecks, official source/
  metadata/configuration validation, upstream v0.4 schema, pins and attribution.
- **PASSED:** admission/transitive-axiom audit; the six principal/consequence
  types and all reachable ordinary definition bodies match their Challenge.
- **PASSED:** official local Comparator with real bubblewrap isolation, Lean's
  default kernel, NanoDa, and the current Palomar-pinned con-ron checker.
- **UNRUN:** supplementary Ruby template/SPDX-gem validators (Ruby/Bundler are
  absent). Metadata validation and the canonical Apache license-text check were
  performed separately.
- **UNRUN:** Palomar's full production canonical verifier, optional public-commit
  preflight and submission/registration. Local checks do not imply registration
  or acceptance.

The local kernel setup followed the [official template verification approach](https://github.com/PalomarRegistry/PalomarTemplate/blob/2891de4c48955af824969a263d31b25e7a9a1406/scripts/verify-comparator.sh),
with the [current authenticated checker selection](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/checker-revisions.json).
The project compiler and dependency pins were unchanged.

## Attribution and automation

Code is Apache-2.0. The small subspace-counting port retains Shlomo A. Perles's
copyright, source path and exact revision in `FourierFormalization/Counting.lean`;
its preferred citation and relationship are recorded in `formalization.yaml`.

Patrick Lopatto is the responsible human maintainer. OpenAI Codex (GPT-6) agents
constructed the Lean proofs using Lean Beam and performed separate statement,
definition and prerequisite reviews. Review status is AI-agent reviewed; no
independent human review or other source-author endorsement is claimed.
