# Paper 6: Prime-Field PINI

**Full title:** "Prime-Field PINI: Machine-Checked Composition Theorems for Post-Quantum NTT Masking"

**Authors:** Ray Iskander, Khaled Kirah

**Status:** Lean 4 proof suite complete: 18 public theorems, zero `sorry`, 1175 build jobs.

---

## Abstract Outline

We prove the first machine-checked composition theorem for arithmetic masking over prime fields. Given two gadgets with Prime-Field PINI parameters k₁ and k₂, we show that fresh inter-stage masking completely erases Stage 1's multiplicity from the composed output — the pipeline's PF-PINI parameter equals that of Stage 2 alone (k₂), regardless of Stage 1's parameter. This *renewal theorem* establishes that the uniform bound max(k₁, k₂) holds for the composed pipeline. We also prove that without fresh masking, intermediate pipeline wires are exposed with multiplicity up to k₁, enabling differential power analysis. Both theorems are formalized in Lean 4 with zero `sorry` stubs, building on our prior machine-checked proofs that NTT butterfly gadgets have PF-PINI(1) and Barrett reduction has PF-PINI(2). We formally bridge the algebraic and Nat arithmetic models of Barrett reduction, reducing the remaining gap to the well-understood connection between Nat arithmetic and hardware RTL. We instantiate these theorems to formally diagnose the Adams Bridge PQC accelerator: its lack of fresh inter-stage masking leaves every Barrett output wire as a DPA attack surface — confirming with formal proof what three independent analyses found empirically. Computational testing confirms Montgomery reduction also satisfies PF-PINI(2), suggesting the 1-Bit Barrier is universal across standard modular reductions.

---

## Paper Structure

### §1 Introduction (2 pages)
- The composition problem for arithmetic masking
- ISW (Boolean, GF(2)) vs. PF-PINI (arithmetic, ZMod q): why a new framework is needed
- The renewal argument: fresh masking as the composition enabler
- Contribution summary: two composition theorems + NatEquivalence bridge + Adams Bridge diagnosis
- Connection to the six-paper program

### §2 Related Work (2 pages)
- ISW 2003: composition for Boolean masking (GF(2)) — our work generalizes to ZMod q
- Barthe et al. 2016: t-SNI composability
- Cassiers-Standaert 2020: PINI (trivial composition)
- Belaïd et al. 2016: composition verification tools
- Bloem et al. 2018: maskVerif
- SILVER (Knichel et al.): automated verification
- Coron 2014, Coron et al. 2018: arithmetic masking schemes
- Gap: no machine-checked composition theorem for arithmetic masking over Z_q

### §3 Preliminaries (2 pages)
- Arithmetic masking over ZMod q
- The PF-PINI(k) definition (from Paper 5): max-multiplicity as security metric
- **Normalization convention:** For a gadget with n-mask space of size q^n, the uniform baseline is q^(n-1) (each output hit q^(n-1) times). PF-PINI(k) means max-multiplicity ≤ k × q^(n-1). The parameter k measures multiplicative deviation from uniformity.
- The first-order probing model: for each probed wire, the attacker observes the output distribution over masks. PF-PINI(k) implies max-weight k/q in this distribution.
- **Relationship to standard notions:** PF-PINI(1) implies value-independence, which corresponds to 1-probing security for individual wires (1-NI per-wire). PF-PINI(k) for k > 1 quantifies leakage beyond the binary NI/SNI/PINI framework — it measures HOW MUCH a wire leaks (at most log₂(k) bits), not just WHETHER it leaks. The composition theorem bounds how this quantitative leakage propagates through pipelines.

### §4 The Renewal Theorem (3 pages)
- **Theorem 4.1 (Renewal Lemma):** `fresh_mask_renewal` — For any PF-PINI gadget G₁ and fresh mask m_fresh, the intermediate wire G₁(x, m₁) - m_fresh is perfectly uniform: card{(m₁, m_fresh) | G₁(x, m₁) - m_fresh = w} = q
- **Corollary 4.2 (Intermediate Uniformity):** `fresh_mask_uniform` — Fresh masking makes all intermediate values equally likely
- **Theorem 4.3 (Positive Composition):** `pfpini_composition_with_fresh_mask` — Composed gadget output multiplicity ≤ k₂ × q²
- **Corollary 4.4 (Symmetric Bound):** `pfpini_composition_max_bound` — ≤ max(k₁, k₂) × q²
- **Key proof technique:** Fiber decomposition `card_filter_prod_le_mul` + product reassociation

### §5 Without Fresh Masking (2 pages)
- **Theorem 5.1 (Intermediate Wire Exposure):** `intermediate_wire_multiplicity_bound` — Without fresh masking, intermediate wire multiplicity ≤ k₁. For Barrett (k₁ = 2): leaks 1 bit per observation.
- **Theorem 5.2 (No-Fresh Output Bound):** `composed_no_fresh_output_bound` — Output multiplicity ≤ k₂ × q (same normalized parameter for 2-stage pipelines)
- **Theorem 5.3 (Security Gap):** `security_gap_intermediate` — When k₁ > 1 and the bound is tight, intermediate wires are non-uniform
- **Discussion:** The security difference is entirely captured by intermediate wire uniformity. Output composition is safe for 2-stage pipelines; the attack surface is the exposed intermediate wire. This directly explains DPA on Adams Bridge.

### §6 The Algebraic-Hardware Bridge (1.5 pages)
- **Theorem 6.1 (NatEquivalence):** `barrett_nat_equivalence` — The algebraic barrettInternalMap equals the Nat arithmetic barrettInternalMapNat under q ≤ 2^s
- **Corollary 6.2:** `barrettNat_pfpini_two` — The hardware-faithful map satisfies PF-PINI(2)
- This closes the formal gap between theorem and RTL: the PF-PINI(2) bound applies to the actual hardware computation

### §7 Adams Bridge Diagnosis (2 pages)
- Instantiation: butterfly is PF-PINI(1), Barrett is PF-PINI(2)
- Adams Bridge has zero fresh inter-stage masking
- **Formal consequence:** Every Barrett output wire has multiplicity 2 (not uniform)
- **Prescription:** Adding one fresh mask per pipeline stage gives max(1, 2) = 2 with perfectly uniform intermediates
- Alignment with empirical findings: Karabulut & Azarderakhsh (ePrint 2025/009), Saarinen (Hardwear.io 2025), QANARY (Paper 1)

### §8 Discussion and Extensions (1.5 pages)
- **Montgomery observation:** Computational testing confirms Montgomery reduction satisfies PF-PINI(2) for ML-KEM (q=3329) and ML-DSA (q=8380417). The `(x+R-m)%R%q` structure is identical to Barrett. Formal proof would follow the same barrettPFPINI argument. The 1-Bit Barrier appears universal across standard modular reductions.
- **The Six-Paper Arc:** Layer 1 (attack) → Layer 2 (detection) → Layer 3 (foundations) → Layer 4 (per-gadget) → Layer 5 (composition). Paper 6 completes the formal theory.
- **Open directions:** Higher-order composition (d-share), pipeline depth generalization, PINI vs PF-PINI connection

### §9 Conclusion (1 page)
- First machine-checked composition theorem for arithmetic masking over prime fields
- Fresh masking is sufficient for compositional security — and its absence exposes intermediate wires to DPA
- The 1-Bit Barrier + composition theorem = complete formal theory of masked NTT hardware

---

## Complete Proof Suite (Lean 4)

| # | File | Theorem | Sorry-free |
|---|------|---------|------------|
| 1 | Basic.lean | filter_sub_right_eq_singleton | ✅ |
| 2 | Basic.lean | card_filter_sub_right_eq_one | ✅ |
| 3 | Basic.lean | card_filter_prod_le_mul | ✅ |
| 4 | PositiveComposition.lean | fresh_mask_renewal | ✅ |
| 5 | PositiveComposition.lean | fresh_mask_uniform | ✅ |
| 6 | PositiveComposition.lean | pfpini_composition_with_fresh_mask | ✅ |
| 7 | PositiveComposition.lean | pfpini_composition_max_bound | ✅ |
| 8 | NegativeComposition.lean | intermediate_wire_multiplicity_bound | ✅ |
| 9 | NegativeComposition.lean | intermediate_wire_with_fresh_is_uniform | ✅ |
| 10 | NegativeComposition.lean | composed_no_fresh_output_bound | ✅ |
| 11 | NegativeComposition.lean | security_gap_intermediate | ✅ |
| 12 | AdamsBridgeDiagnosis.lean | adams_bridge_butterfly_wire_ok | ✅ |
| 13 | AdamsBridgeDiagnosis.lean | adams_bridge_barrett_wire_leaks | ✅ |
| 14 | AdamsBridgeDiagnosis.lean | adams_bridge_with_fresh_secure | ✅ |
| 15 | AdamsBridgeDiagnosis.lean | adams_bridge_fresh_pfpini_parameter | ✅ |
| 16 | AdamsBridgeDiagnosis.lean | adams_bridge_intermediate_uniform_with_fresh | ✅ |
| 17 | NatEquivalence.lean | barrett_nat_equivalence | ✅ |
| 18 | NatEquivalence.lean | barrettNat_pfpini_two | ✅ |

**18 public theorems, zero sorry, 1175 build jobs, zero errors.**

---

## Dependencies

- **Paper 3** (qanary-universal): Ring axioms, value independence
- **Paper 4** (qanary-paper4): Butterfly PF-PINI(1), pipeline composition
- **Paper 5** (qanary-paper5): PFPINIGadget structure, Barrett PF-PINI(2), identityPFPINI, barrettPFPINI, barrettInternalMap, barrettInternalMapNat
- **Mathlib** @ 322515540d7f: Finset, ZMod, BigOperators, Fintype
- **Toolchain:** leanprover/lean4:v4.30.0-rc1

---

## Montgomery Reconnaissance Results

| Prime q | s | R = 2^s | Max-multiplicity | Test type |
|---------|---|---------|------------------|-----------|
| 5, 7, 11, 13, 17, 23, 29, 31 | varies | varies | 2 | exhaustive |
| 3329 (ML-KEM) | 12 | 4096 | 2 | exhaustive |
| 8380417 (ML-DSA) | 23 | 8388608 | 2 | 100 random x, exhaustive m |

**Conclusion (computational, not formally proved):** Montgomery max-multiplicity = 2 across every tested case. Same `(x+R-m)%R%q` two-branch structure as Barrett. The 1-Bit Barrier *appears* universal across Barrett and Montgomery reductions on the basis of this reconnaissance; a formal Lean restatement for Montgomery is left as future work.

---

## Design Notes: Common Pitfalls

Two subtle points where the natural first guess is wrong:

1. **Positive bound:** Correct is `max(k₁,k₂) × q²` (not × q). The q² is the uniform baseline for a 3-mask space of size q³.
2. **Negative theorem:** Correct output bound is `k₂ × q` (not k₁ × k₂). The security gap is intermediate wire exposure (multiplicity k₁), not output composition.
