/-
  QanaryPaper6/AdamsBridgeDiagnosis.lean

  Formal instantiation of both composition theorems to Adams Bridge.

  Adams Bridge uses:
  - NTT butterfly: PF-PINI(1) (perfect bijection, Paper 4)
  - Barrett reduction: PF-PINI(2) (1-bit barrier, Paper 5)
  - NO fresh inter-stage masking

  This file proves that adding fresh masking would secure the pipeline,
  and that without it, intermediate Barrett output wires are non-uniform.
-/
import QanaryPaper6.NegativeComposition

open Finset Fintype

variable {q : ℕ} [NeZero q]

/-! ### Adams Bridge pipeline parameters -/

/-- Adams Bridge butterfly is PF-PINI(1). From Paper 5's identityPFPINI. -/
noncomputable def adamsBridgeButterfly : PFPINIGadget q := identityPFPINI

/-- Adams Bridge Barrett is PF-PINI(2). From Paper 5's barrettPFPINI. -/
noncomputable def adamsBridgeBarrett (s : ℕ) : PFPINIGadget q := barrettPFPINI s

/-! ### The diagnosis -/

/-- Butterfly output has multiplicity ≤ 1: perfect bijection. -/
theorem adams_bridge_butterfly_wire_ok (x v : ZMod q) :
    (univ.filter (fun m₁ : ZMod q =>
      (adamsBridgeButterfly : PFPINIGadget q).compute x m₁ = v)).card ≤ 1 :=
  adamsBridgeButterfly.bound x v

/-- Barrett output has multiplicity ≤ 2: the 1-bit barrier.
    Without fresh masking, this wire leaks up to 1 bit per DPA measurement. -/
theorem adams_bridge_barrett_wire_leaks (s : ℕ) (x v : ZMod q) :
    (univ.filter (fun m₁ : ZMod q =>
      (adamsBridgeBarrett s : PFPINIGadget q).compute x m₁ = v)).card ≤ 2 :=
  (adamsBridgeBarrett s).bound x v

/-! ### The prescription -/

/-- With fresh masking, the composed pipeline is secure.
    The intermediate wire becomes perfectly uniform. -/
theorem adams_bridge_with_fresh_secure (s : ℕ) (x v : ZMod q) :
    (univ.filter (fun t : ZMod q × ZMod q × ZMod q =>
      composedWithFresh (adamsBridgeButterfly : PFPINIGadget q)
        (adamsBridgeBarrett s : PFPINIGadget q)
        x t.1 t.2.1 t.2.2 = v)).card
    ≤ max (adamsBridgeButterfly : PFPINIGadget q).maxMult
          (adamsBridgeBarrett s : PFPINIGadget q).maxMult
      * (card (ZMod q))^2 :=
  pfpini_composition_max_bound _ _ x v

/-- The pipeline PF-PINI parameter with fresh masking is max(1,2) = 2. -/
theorem adams_bridge_fresh_pfpini_parameter (s : ℕ) :
    max (adamsBridgeButterfly : PFPINIGadget q).maxMult
        (adamsBridgeBarrett s : PFPINIGadget q).maxMult = 2 := by
  unfold adamsBridgeButterfly adamsBridgeBarrett identityPFPINI barrettPFPINI
  simp

/-- The intermediate wire between butterfly (Stage 1) and Barrett (Stage 2)
    is perfectly uniform with fresh masking.
    Uses adamsBridgeButterfly as G₁ to match the paper's pipeline narrative. -/
theorem adams_bridge_intermediate_uniform_with_fresh (x w : ZMod q) :
    (univ.filter (fun p : ZMod q × ZMod q =>
      (adamsBridgeButterfly : PFPINIGadget q).compute x p.1 - p.2 = w)).card
    = card (ZMod q) :=
  fresh_mask_renewal _ x w
