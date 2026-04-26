# QanaryPaper6

**Prime-Field PINI: Machine-Checked Composition Theorems for Post-Quantum NTT Masking**

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.30.0--rc1-blue)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-322515540d7f-green)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Sorry-Free](https://img.shields.io/badge/sorry-0-brightgreen)]()

Machine-checked universal proofs that **fresh inter-stage masking
composes** arithmetic-masked gadgets over prime fields. Given two
gadgets with Prime-Field PINI parameters `k₁` and `k₂`, fresh masking
yields a composed pipeline whose output satisfies **PF-PINI(`k₂`)** —
the Renewal Theorem shows the fresh mask completely erases Stage 1's
multiplicity, so the composed bound depends on `k₂` alone (the
symmetric `max(k₁, k₂)` corollary follows trivially). Without fresh
masking, intermediate wires are exposed with multiplicity up to `k₁`,
enabling DPA.

This is the artifact repository for:

> R. Iskander, K. Kirah. "Prime-Field PINI: Machine-Checked
> Composition Theorems for Post-Quantum NTT Masking."
> arXiv:XXXX.XXXXX, 2026. *(arXiv ID pending.)*

## Context: Prior Papers in the Series

This artifact is the capstone of a five-part formal-verification arc:

- **Paper 1** — "Structural Dependency Analysis for Masked NTT
  Hardware: Scalable Pre-Silicon Verification of Post-Quantum
  Cryptographic Accelerators." arXiv:2604.15249, 2026.
- **Paper 2** — "Partial Number Theoretic Transform Masking in
  Post-Quantum Cryptography (PQC) Hardware: A Security Margin
  Analysis." arXiv:2604.03813, 2026.
- **Paper 3** — "From Finite Enumeration to Universal Proof:
  Ring-Theoretic Foundations for PQC Hardware Masking Verification."
  arXiv:2604.18717, 2026. Sibling artifact:
  [qanary-universal-masking-proofs](https://github.com/rayiskander2406/qanary-universal-masking-proofs-arXiv-2604.18717).
- **Paper 4** — "Fresh Masking Makes NTT Pipelines Composable."
  arXiv:2604.20793, 2026. Sibling artifact:
  [qanary-masked-ntt-pipeline-security](https://github.com/rayiskander2406/qanary-masked-ntt-pipeline-security-arXiv-2604.20793).
- **Paper 5** — "Machine-Checked Cardinality Bounds for Masked
  Barrett Reduction: A 1-Bit Side-Channel Leakage Barrier in
  Post-Quantum Cryptographic Hardware." Preprint 2026 (arXiv ID
  pending). Sibling artifact:
  [qanary-one-bit-barrier](https://github.com/rayiskander2406/qanary-one-bit-barrier-arXiv-XXXX.XXXXX).

Paper 6 (this artifact) lifts the per-gadget PF-PINI bounds of
Papers 4–5 to a **compositional security theory**.

This artifact depends on the Paper 3, Paper 4, and Paper 5 artifacts
as sibling directories; see [Building](#building).

## Main Results

**1. The Renewal Lemma (Theorem `fresh_mask_renewal`).**
For any PF-PINI gadget `G₁`, any secret `x`, and any target intermediate
value `w`, exactly `q` pairs `(m₁, m_fresh)` produce `w` via
`G₁(x, m₁) - m_fresh = w`. The intermediate wire is **perfectly
uniform** regardless of `G₁`'s internal multiplicity.

**2. Positive Composition Theorem (`pfpini_composition_with_fresh_mask`).**
With fresh inter-stage masking, the composed gadget's output
multiplicity over `(ZMod q)³` is bounded by `G₂.maxMult × q²` —
i.e., the composed pipeline satisfies PF-PINI(`k₂`) **alone**, with
`k₁` completely erased from the bound. The symmetric `max(k₁, k₂) × q²`
corollary (`pfpini_composition_max_bound`) is a strictly weaker form
useful when only the maximum is known.

**3. Negative Result (`composed_no_fresh_output_bound` +
`security_gap_intermediate`).**
Without fresh masking, the composed output is still safe for two-stage
pipelines (multiplicity `≤ k₂ × q`), but intermediate wires are
exposed with multiplicity `≤ k₁`. When `k₁ > 1`, those wires are
non-uniform and directly expose secret-dependent information to DPA.

**4. Algebraic-Hardware Bridge (`barrett_nat_equivalence`).**
Proves equivalence between the algebraic `barrettInternalMap` (Paper 5)
and the hardware-faithful Nat arithmetic definition
`barrettInternalMapNat`, under the scope condition `q ≤ 2^s`. Closes
Paper 5's formally deferred Nat-equivalence limitation.

**5. Adams Bridge Diagnosis.**
Formally instantiates the theorems on the Adams Bridge NTT accelerator:
butterfly is PF-PINI(1), Barrett is PF-PINI(2), Adams Bridge's lack of
fresh inter-stage masking exposes every Barrett output wire as a
DPA attack surface — a formal counterpart of three independent
empirical analyses.

## Theorem Index

| # | Theorem | File | Role |
|---|---------|------|------|
| 1 | `filter_sub_right_eq_singleton` | `Basic.lean` | Translation bijection (foundation for renewal) |
| 2 | `card_filter_sub_right_eq_one` | `Basic.lean` | Translation filter cardinality = 1 |
| 3 | `card_filter_prod_le_mul` | `Basic.lean` | Fiber decomposition counting lemma |
| 4 | `fresh_mask_renewal` | `PositiveComposition.lean` | **The Renewal Lemma (Theorem 4.1)** |
| 5 | `fresh_mask_uniform` | `PositiveComposition.lean` | Intermediate values equally likely |
| 6 | `pfpini_composition_with_fresh_mask` | `PositiveComposition.lean` | **Positive composition bound `k₂ × q²`** |
| 7 | `pfpini_composition_max_bound` | `PositiveComposition.lean` | Symmetric `max(k₁, k₂) × q²` bound |
| 8 | `intermediate_wire_multiplicity_bound` | `NegativeComposition.lean` | No-fresh intermediate exposure `≤ k₁` |
| 9 | `intermediate_wire_with_fresh_is_uniform` | `NegativeComposition.lean` | Fresh-mask intermediate uniformity |
| 10 | `composed_no_fresh_output_bound` | `NegativeComposition.lean` | No-fresh output bound `≤ k₂ × q` |
| 11 | `security_gap_intermediate` | `NegativeComposition.lean` | `k₁ > 1` ∧ tight ⟹ non-uniform intermediate |
| 12 | `adams_bridge_butterfly_wire_ok` | `AdamsBridgeDiagnosis.lean` | Butterfly PF-PINI(1) instantiation |
| 13 | `adams_bridge_barrett_wire_leaks` | `AdamsBridgeDiagnosis.lean` | Barrett PF-PINI(2) instantiation |
| 14 | `adams_bridge_with_fresh_secure` | `AdamsBridgeDiagnosis.lean` | Fresh-mask pipeline instantiation |
| 15 | `adams_bridge_fresh_pfpini_parameter` | `AdamsBridgeDiagnosis.lean` | `max(1, 2) = 2` |
| 16 | `adams_bridge_intermediate_uniform_with_fresh` | `AdamsBridgeDiagnosis.lean` | Uniform-intermediate instantiation |
| 17 | `barrett_nat_equivalence` | `NatEquivalence.lean` | Algebraic ⟺ Nat arithmetic Barrett |
| 18 | `barrettNat_pfpini_two` | `NatEquivalence.lean` | Hardware-faithful Barrett PF-PINI(2) |

All 18 theorems are **sorry-free** and **kernel-verified**; none use
`native_decide`, `admit`, or `axiom`.

## Building

Requires [elan](https://github.com/leanprover/elan) and three sibling
artifact repositories cloned alongside this one. Lake reads them via
local-path dependencies declared in `lakefile.lean`:

```bash
# Install elan (if not already)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# Create a workspace directory and clone all four artifacts as siblings
mkdir qanary-artifacts && cd qanary-artifacts

git clone https://github.com/rayiskander2406/qanary-universal-masking-proofs-arXiv-2604.18717 qanary-universal
git clone https://github.com/rayiskander2406/qanary-masked-ntt-pipeline-security-arXiv-2604.20793 qanary-paper4
git clone https://github.com/rayiskander2406/qanary-one-bit-barrier-arXiv-XXXX.XXXXX qanary-paper5
git clone https://github.com/rayiskander2406/qanary-pf-pini-composition-arXiv-XXXX.XXXXX qanary-paper6

cd qanary-paper6
lake build
```

The sibling directory names must be exactly `qanary-universal`,
`qanary-paper4`, and `qanary-paper5` (as referenced in `lakefile.lean`).

First build downloads Mathlib (~30 minutes). Subsequent builds are
incremental.

## Reproduction

```bash
# Full verification: build + zero-stub scan + theorem check (~30 min cold, <1 min warm)
python3 reproduce.py

# Quick check: skip build, verify existing artifacts (<5 seconds)
python3 reproduce.py --check
```

The script enforces nine logical pass gates; each gate expands into
one or more individual `check()` lines in the script output:

| # | Check | Expected |
|---|-------|----------|
| 1 | `lean-toolchain` exists and pins `leanprover/lean4:` | pass |
| 2 | `lakefile.lean` pins Mathlib to commit `322515540d7f` | pass |
| 3 | Paper 3 / Paper 4 / Paper 5 artifacts present as siblings | 3/3 |
| 4 | `lake build` exits with code 0 (skipped with `--check`) | pass |
| 5 | Zero `sorry`, `admit`, `axiom`, `native_decide` in tracked `.lean` sources | 0 found |
| 6 | All 18 expected theorem identifiers present in correct files | 18/18 |
| 7 | Repository structure complete (15 required files) | 15/15 |
| 8 | No `.docx`, `.tex`, `.bib`, `.pdf` files tracked in git | clean |
| 9 | No AI attribution tokens in tracked sources | 0 found |

Any failure prints a detailed `[FAIL]` line and returns non-zero exit code.

## Project Structure

```
QanaryPaper6/
  Basic.lean                   -- Composed gadget definitions
                                  (with and without fresh masking);
                                  translation bijection lemmas;
                                  fiber-decomposition counting lemma
  PositiveComposition.lean     -- Renewal Lemma + positive composition
                                  theorem with k₂ × q² bound
  NegativeComposition.lean     -- No-fresh output bound;
                                  intermediate wire exposure;
                                  security-gap theorem
  AdamsBridgeDiagnosis.lean    -- Butterfly / Barrett / pipeline
                                  instantiations for Adams Bridge
  NatEquivalence.lean          -- Algebraic ⟺ Nat arithmetic Barrett
                                  (closes Paper 5 Limitation (vi))
QanaryPaper6.lean              -- Root import
```

## Key Insight

The Renewal Lemma is the algebraic heart of the theory. For any
PF-PINI gadget `G₁`:

```
∀ x w,  card{(m₁, m_fresh) : G₁(x, m₁) − m_fresh = w}  =  q
```

The proof is one-line algebraic: for each fixed `m₁`, there is
exactly one `m_fresh = G₁(x, m₁) − w` that satisfies the equation,
and the map `m₁ ↦ (m₁, G₁(x, m₁) − w)` is injective (first component
determines everything). The image has cardinality `card (ZMod q) = q`.

Because `q` does not depend on `w`, each intermediate value is
equally likely. Stage 2 therefore sees a perfectly uniform input
regardless of Stage 1's internal structure. Composing the PF-PINI(k₂)
bound of Stage 2 over the uniform distribution yields the
`k₂ × q²` output bound via fiber decomposition
(`card_filter_prod_le_mul`).

The negative result is symmetric: without `m_fresh`, the intermediate
wire is *just* `G₁(x, m₁)`, and its multiplicity is `k₁` by Stage 1's
PF-PINI bound. If `k₁ > 1`, that wire is non-uniform — which is
exactly the DPA surface.

## Scope and Limitations

- **First-order probing only.** One probe per wire. Higher-order
  probing (d ≥ 2) is out of scope.
- **Two-stage pipelines in the core theorems.** The composition
  theorems are stated for two composed gadgets `G₁ ∘ G₂`. Longer
  pipelines follow by induction on stages with fresh masking between
  each pair, but the induction is not formalized here.
- **Bound is not provably tight.** The `k₂ × q²` output bound is the
  tightest bound we prove; tightness (that `= k₂ × q²` is attainable)
  is stated as future work.
- **Adams Bridge instantiation is architectural, not gate-level.**
  The theorems diagnose the RTL-level absence of fresh re-masking;
  gate-level leakage from non-ideal logic is Paper 1's responsibility.
- **Montgomery reduction observation is informal.** The `(x + R − m)
  mod R mod q` two-branch structure is identical to Barrett, so the
  same PF-PINI(2) bound holds by the same argument, but the formal
  Lean restatement for Montgomery is left as future work.

## Reproducibility Notes

- **Pinned toolchain.** `lean-toolchain` pins
  `leanprover/lean4:v4.30.0-rc1` and `lakefile.lean` pins Mathlib to
  commit `322515540d7f`. **Same pin as the Paper 3, 4, and 5
  artifacts.** A machine that can build any of those can build
  this one.
- **Cold build time.** First `lake build` downloads Mathlib
  (~1.3 GB, ~25-40 minutes). Subsequent incremental builds complete
  in under 30 seconds.
- **Cache re-use.** `lake exe cache get` populates the pre-built
  Mathlib olean cache (~4 GB) and reduces cold build time to under
  5 minutes.
- **Kernel-only tactics.** The whole proof suite uses kernel-only
  tactics (`ring`, `linear_combination`, `simp`, `omega`,
  `Finset.card_*`, `card_eq_sum_card_fiberwise`). No `native_decide`.
- **Three-way sibling dependency.** Lake reads `../qanary-universal`,
  `../qanary-paper4`, `../qanary-paper5` as local-path dependencies.
  All three siblings must be on the same Mathlib pin (they are, by
  design).
- **Platform.** Verified on macOS (Apple Silicon and Intel) and
  Linux x86_64.
- **Python version.** `reproduce.py` is Python 3 standard library
  only; no external packages required.

## Design Document

See [DESIGN.md](DESIGN.md) for the paper structure, the full theorem
inventory with proof sketches, dependencies on Papers 3-5, and a
discussion of subtle points where the natural first guess is wrong.

## Citation

If you use this artifact, please cite the paper:

```bibtex
@article{IskanderKirah2026Composition,
  author  = {Ray Iskander and Khaled Kirah},
  title   = {Prime-Field PINI: Machine-Checked Composition Theorems
             for Post-Quantum NTT Masking},
  journal = {arXiv preprint},
  year    = {2026},
  note    = {arXiv:XXXX.XXXXX (ID pending)},
}
```

See [CITATION.cff](CITATION.cff) for the machine-readable citation.

## License

MIT. See [LICENSE](LICENSE).

## Authors

Ray Iskander (Verdict Security), Khaled Kirah (Ain Shams University)
