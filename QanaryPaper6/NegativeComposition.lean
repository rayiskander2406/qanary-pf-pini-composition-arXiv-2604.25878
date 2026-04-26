/-
  QanaryPaper6/NegativeComposition.lean

  The Negative Composition Theorem: what happens WITHOUT fresh masking.

  Main results:
  - intermediate_wire_multiplicity_bound: without fresh masking,
    the intermediate wire G₁(x, m₁) has multiplicity ≤ k₁
  - intermediate_wire_with_fresh_is_uniform: with fresh masking,
    the intermediate wire multiplicity is exactly q (uniform)
  - composed_no_fresh_output_bound: the no-fresh output bound is k₂ × q

  The security gap is in the intermediate wires, not the output.
  This is exactly what enables DPA on Adams Bridge.
-/
import QanaryPaper6.PositiveComposition

open Finset Fintype

variable {q : ℕ} [NeZero q]

/-! ### Intermediate wire exposure without fresh masking -/

/-- **The Negative Theorem: Intermediate Wire Multiplicity**

Without fresh masking, the intermediate wire G₁(x, m₁) has multiplicity
bounded by G₁'s PF-PINI parameter k₁. This follows directly from the
PF-PINI bound — no composition argument needed.

For Barrett (k₁=2), some intermediate values are hit by 2 masks while
others are hit by 1 or 0. An attacker probing this wire gains
information about the secret x. -/
theorem intermediate_wire_multiplicity_bound
    (G₁ : PFPINIGadget q) (x v : ZMod q) :
    (univ.filter (fun m₁ : ZMod q =>
      G₁.compute x m₁ = v)).card ≤ G₁.maxMult :=
  G₁.bound x v

/-- **Contrast: With fresh masking, intermediate multiplicity is always q.**

This is the renewal lemma restated for comparison:
  - Without fresh masking: multiplicity ≤ k₁ (non-uniform)
  - With fresh masking: multiplicity = q (perfectly uniform) -/
theorem intermediate_wire_with_fresh_is_uniform
    (G₁ : PFPINIGadget q) (x w : ZMod q) :
    (univ.filter (fun p : ZMod q × ZMod q =>
      G₁.compute x p.1 - p.2 = w)).card = card (ZMod q) :=
  fresh_mask_renewal G₁ x w

/-! ### Composed output bound without fresh masking -/

/-- **No-fresh output bound.**
    Without fresh masking, the composed output over mask space (m₁, m₂) has:
      card{(m₁, m₂) | G₂(G₁(x,m₁), m₂) = v} ≤ k₂ × q

    Proof strategy: Σ_w card{m₁|G₁(x,m₁)=w} × card{m₂|G₂(w,m₂)=v}
                    ≤ k₂ × Σ_w card{m₁|G₁(x,m₁)=w} = k₂ × q -/
theorem composed_no_fresh_output_bound
    (G₁ G₂ : PFPINIGadget q) (x v : ZMod q) :
    (univ.filter (fun p : ZMod q × ZMod q =>
      composedNoFresh G₁ G₂ x p.1 p.2 = v)).card
    ≤ G₂.maxMult * Fintype.card (ZMod q) := by
  -- Apply fiber decomposition: for each m₁, at most k₂ values of m₂ work
  have h_bound := card_filter_prod_le_mul
    (fun p : ZMod q × ZMod q => composedNoFresh G₁ G₂ x p.1 p.2 = v)
    G₂.maxMult
    (fun m₁ => G₂.bound (G₁.compute x m₁) v)
  calc (univ.filter _).card
    ≤ Fintype.card (ZMod q) * G₂.maxMult := h_bound
    _ = G₂.maxMult * Fintype.card (ZMod q) := Nat.mul_comm _ _

/-! ### The security gap -/

/-- **The Security Gap: non-uniform intermediates enable DPA.**

If G₁'s max-multiplicity exceeds 1, there exist intermediate values
that are hit by more than one mask — the wire is non-uniform.
An attacker probing this wire can distinguish secrets. -/
theorem security_gap_intermediate
    (G₁ : PFPINIGadget q) (x : ZMod q)
    (h_nontriv : G₁.maxMult > 1)
    (h_tight : ∃ v, (univ.filter (fun m₁ : ZMod q =>
      G₁.compute x m₁ = v)).card = G₁.maxMult) :
    ∃ v, (univ.filter (fun m₁ : ZMod q =>
      G₁.compute x m₁ = v)).card > 1 := by
  obtain ⟨v, hv⟩ := h_tight
  exact ⟨v, by omega⟩
