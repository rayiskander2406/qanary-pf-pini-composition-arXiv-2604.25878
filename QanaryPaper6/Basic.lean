/-
  QanaryPaper6/Basic.lean

  Core definitions for PF-PINI composition theorems.

  Imports the PFPINIGadget structure from Paper 5 and defines:
  - Composed gadget with fresh inter-stage masking
  - Composed gadget without fresh masking
  - Translation bijection lemmas (foundation for renewal argument)
-/
import QanaryPaper5.BarrettUniversal
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset

variable {q : ℕ} [NeZero q]

/-! ### Composed gadget definitions -/

/-- The composed gadget WITH fresh inter-stage masking.
    Given G₁, G₂ : PFPINIGadget q, the composed computation is:
      (x, m₁, m_fresh, m₂) ↦ G₂(G₁(x, m₁) - m_fresh, m₂)
    The fresh mask m_fresh re-randomizes G₁'s output before G₂ processes it. -/
noncomputable def composedWithFresh
    (G₁ G₂ : PFPINIGadget q)
    (x : ZMod q) (m₁ m_fresh m₂ : ZMod q) : ZMod q :=
  G₂.compute (G₁.compute x m₁ - m_fresh) m₂

/-- The composed gadget WITHOUT fresh inter-stage masking.
    Given G₁, G₂ : PFPINIGadget q, the composed computation is:
      (x, m₁, m₂) ↦ G₂(G₁(x, m₁), m₂)
    Stage 2 directly receives Stage 1's output — no re-randomization. -/
noncomputable def composedNoFresh
    (G₁ G₂ : PFPINIGadget q)
    (x : ZMod q) (m₁ m₂ : ZMod q) : ZMod q :=
  G₂.compute (G₁.compute x m₁) m₂

/-! ### Translation bijection (foundation for renewal argument) -/

/-- For any target value w, the set {m_fresh | u - m_fresh = w} is a singleton {u - w}. -/
theorem filter_sub_right_eq_singleton (u w : ZMod q) :
    univ.filter (fun m_fresh : ZMod q => u - m_fresh = w) = {u - w} := by
  ext m
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    calc m = u - (u - m) := by ring
      _ = u - w := by rw [h]
  · intro h; rw [h]; ring

/-- The translation filter has cardinality exactly 1. -/
theorem card_filter_sub_right_eq_one (u w : ZMod q) :
    (univ.filter (fun m_fresh : ZMod q => u - m_fresh = w)).card = 1 := by
  rw [filter_sub_right_eq_singleton u w, card_singleton]

/-! ### Fiber decomposition for product filters -/

/-- For a filter on a product type α × β, the cardinality is bounded by
    card(α) × k when each α-fiber has at most k elements.
    This is the counting lemma used in both composition theorems. -/
theorem card_filter_prod_le_mul
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq (α × β)]
    (P : α × β → Prop) [DecidablePred P]
    (k : ℕ) (hk : ∀ a : α, (univ.filter (fun b : β => P (a, b))).card ≤ k) :
    (univ.filter P).card ≤ Fintype.card α * k := by
  classical
  -- Step 1: Decompose filter card into sum over fibers using card_eq_sum_card_fiberwise
  have h_fib := Finset.card_eq_sum_card_fiberwise
    (f := fun (p : α × β) => p.1) (s := univ.filter P) (t := univ)
    (fun _ _ => mem_univ _)
  -- Step 2: Each fiber card equals the corresponding single-variable filter card
  have h_fiber_eq : ∀ a ∈ (univ : Finset α),
      ((univ.filter P).filter (fun p : α × β => p.1 = a)).card =
      (univ.filter (fun b : β => P (a, b))).card := by
    intro a _
    apply Finset.card_bij (fun p _ => p.2)
    · intro ⟨a', b⟩ hm
      simp only [mem_filter, mem_univ, true_and] at hm ⊢
      rw [hm.2] at hm; exact hm.1
    · intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
      simp only [mem_filter, mem_univ, true_and] at h₁ h₂
      simp only at heq
      exact Prod.ext (h₁.2.trans h₂.2.symm) heq
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb ⊢
      exact ⟨(a, b), ⟨hb, rfl⟩, rfl⟩
  -- Step 3: Combine and bound
  rw [h_fib]
  calc ∑ a ∈ univ, ((univ.filter P).filter (fun p : α × β => p.1 = a)).card
    = ∑ a ∈ univ, (univ.filter (fun b : β => P (a, b))).card :=
        Finset.sum_congr rfl h_fiber_eq
    _ ≤ ∑ _a ∈ univ, k := Finset.sum_le_sum (fun a _ => hk a)
    _ = Fintype.card α * k := by simp [Finset.sum_const, Finset.card_univ]
