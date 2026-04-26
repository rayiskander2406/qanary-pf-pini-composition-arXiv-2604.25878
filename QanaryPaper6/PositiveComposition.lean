/-
  QanaryPaper6/PositiveComposition.lean

  The Renewal Argument and Positive Composition Theorem.

  Main results:
  - fresh_mask_renewal: with fresh masking, every intermediate value w
    is produced by exactly q pairs (m₁, m_fresh). The intermediate wire
    is perfectly uniform.
  - pfpini_composition_with_fresh_mask: the composed gadget's output
    multiplicity is bounded by k₂ × q² (the tight bound).
  - pfpini_composition_max_bound: the weaker symmetric bound max(k₁, k₂) × q².

  This is the mathematical heart of Paper 6 — the result that makes
  the entire six-paper program a complete formal theory.
-/
import QanaryPaper6.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Image

open Finset Fintype

variable {q : ℕ} [NeZero q]

/-! ### The Renewal Argument -/

/-- **The Renewal Lemma (Key Theorem)**

For any PF-PINI gadget G₁, any secret x, and any target intermediate value w,
exactly q pairs (m₁, m_fresh) produce that intermediate value:
  card{(m₁, m_fresh) | G₁(x, m₁) - m_fresh = w} = q

Proof: For each m₁ ∈ ZMod q, there is exactly one m_fresh = G₁(x, m₁) - w
such that G₁(x, m₁) - m_fresh = w. The set of valid pairs is the image of
the injective map m₁ ↦ (m₁, G₁(x, m₁) - w), so its cardinality equals q.

This means Stage 2 sees each input value w with equal frequency —
the intermediate wire is perfectly uniform regardless of G₁'s structure. -/
theorem fresh_mask_renewal
    (G₁ : PFPINIGadget q) (x w : ZMod q) :
    (univ.filter (fun p : ZMod q × ZMod q =>
      G₁.compute x p.1 - p.2 = w)).card = card (ZMod q) := by
  -- Step 1: The filter set equals the image of m₁ ↦ (m₁, G₁(x,m₁) - w)
  have h_eq : univ.filter (fun p : ZMod q × ZMod q =>
      G₁.compute x p.1 - p.2 = w) =
    univ.image (fun m₁ : ZMod q => (m₁, G₁.compute x m₁ - w)) := by
    ext ⟨m₁, mf⟩
    simp only [mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨m₁, rfl, by linear_combination h⟩
    · rintro ⟨_, rfl, hmf⟩
      linear_combination hmf
  -- Step 2: The map is injective (first component determines everything)
  have h_inj : Function.Injective
      (fun m₁ : ZMod q => (m₁, G₁.compute x m₁ - w)) := by
    intro a b hab
    exact (Prod.mk.inj hab).1
  -- Step 3: card of image of injective map on univ = card of type
  rw [h_eq, card_image_of_injective _ h_inj, card_univ]

/-- **Corollary: Every intermediate value is equally likely.**
    The count q = card(ZMod q) is independent of w, meaning each
    intermediate value is hit by the same number of mask pairs. -/
theorem fresh_mask_uniform
    (G₁ : PFPINIGadget q) (x : ZMod q) (w₁ w₂ : ZMod q) :
    (univ.filter (fun p : ZMod q × ZMod q =>
      G₁.compute x p.1 - p.2 = w₁)).card =
    (univ.filter (fun p : ZMod q × ZMod q =>
      G₁.compute x p.1 - p.2 = w₂)).card := by
  rw [fresh_mask_renewal G₁ x w₁, fresh_mask_renewal G₁ x w₂]

/-! ### Positive Composition Theorem -/

/-- **The Positive Composition Theorem (Main Result)**

With fresh inter-stage masking, the composed gadget's output multiplicity
over the product mask space (m₁, m_fresh, m₂) ∈ (ZMod q)³ is bounded by:

  card{(m₁, m_fresh, m₂) | G₂(G₁(x,m₁) - m_fresh, m₂) = v}
  ≤ G₂.maxMult × q²

The q² factor is the uniform baseline for a 3-mask space of size q³
mapping to q output values. The normalized PF-PINI parameter of the
composed gadget is therefore G₂.maxMult ≤ max(k₁, k₂).

Proof sketch: By the renewal lemma, the sum over intermediate values w
has each fiber contributing exactly q pairs (m₁, m_fresh). By G₂'s
PF-PINI(k₂) bound, at most k₂ masks m₂ produce output v from each w.
The total is q × Σ_w card{m₂|G₂(w,m₂)=v} ≤ q × q × k₂ = q² × k₂. -/
theorem pfpini_composition_with_fresh_mask
    (G₁ G₂ : PFPINIGadget q) (x v : ZMod q) :
    (univ.filter (fun t : ZMod q × ZMod q × ZMod q =>
      composedWithFresh G₁ G₂ x t.1 t.2.1 t.2.2 = v)).card
    ≤ G₂.maxMult * (Fintype.card (ZMod q))^2 := by
  -- Apply the fiber decomposition: group by (m₁, m_fresh), bound m₂ fibers
  -- ZMod q × ZMod q × ZMod q = ZMod q × (ZMod q × ZMod q) in Lean
  -- We need α = ZMod q, β = ZMod q × ZMod q
  -- For each m₁ : ZMod q, the fiber over (m_fresh, m₂) has card to bound
  -- But we want to group by (m₁, m_fresh) instead. Use associativity:
  -- Treat as (ZMod q × ZMod q) × ZMod q via reassociation
  have h_reassoc : (univ.filter (fun t : ZMod q × ZMod q × ZMod q =>
      composedWithFresh G₁ G₂ x t.1 t.2.1 t.2.2 = v)).card =
    (univ.filter (fun t : (ZMod q × ZMod q) × ZMod q =>
      G₂.compute (G₁.compute x t.1.1 - t.1.2) t.2 = v)).card := by
    apply Finset.card_bij
      (fun t _ => ((t.1, t.2.1), t.2.2))
      (by intro ⟨m₁, mf, m₂⟩ hm; simpa [composedWithFresh] using hm)
      (by intro ⟨a₁, a₂, a₃⟩ _ ⟨b₁, b₂, b₃⟩ _ h;
          simp only [Prod.mk.injEq] at h; ext <;> simp_all)
      (by intro ⟨⟨m₁, mf⟩, m₂⟩ hm; exact ⟨(m₁, mf, m₂),
          by simpa [composedWithFresh] using hm, rfl⟩)
  rw [h_reassoc]
  -- Now apply card_filter_prod_le_mul with α = ZMod q × ZMod q, β = ZMod q
  have h_bound := card_filter_prod_le_mul
    (fun t : (ZMod q × ZMod q) × ZMod q =>
      G₂.compute (G₁.compute x t.1.1 - t.1.2) t.2 = v)
    G₂.maxMult
    (fun ⟨m₁, mf⟩ => G₂.bound (G₁.compute x m₁ - mf) v)
  calc (univ.filter _).card
    ≤ Fintype.card (ZMod q × ZMod q) * G₂.maxMult := h_bound
    _ = (Fintype.card (ZMod q))^2 * G₂.maxMult := by
        rw [Fintype.card_prod]; ring
    _ = G₂.maxMult * (Fintype.card (ZMod q))^2 := by ring

/-- **Weaker symmetric bound using max(k₁, k₂).** -/
theorem pfpini_composition_max_bound
    (G₁ G₂ : PFPINIGadget q) (x v : ZMod q) :
    (univ.filter (fun t : ZMod q × ZMod q × ZMod q =>
      composedWithFresh G₁ G₂ x t.1 t.2.1 t.2.2 = v)).card
    ≤ max G₁.maxMult G₂.maxMult * (Fintype.card (ZMod q))^2 := by
  calc (univ.filter (fun t : ZMod q × ZMod q × ZMod q =>
      composedWithFresh G₁ G₂ x t.1 t.2.1 t.2.2 = v)).card
    ≤ G₂.maxMult * (Fintype.card (ZMod q))^2 :=
        pfpini_composition_with_fresh_mask G₁ G₂ x v
    _ ≤ max G₁.maxMult G₂.maxMult * (Fintype.card (ZMod q))^2 := by
        apply Nat.mul_le_mul_right
        exact le_max_right _ _
