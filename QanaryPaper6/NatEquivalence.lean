/-
  QanaryPaper6/NatEquivalence.lean

  Bridge between the algebraic Barrett map (used in proofs) and the
  Nat arithmetic Barrett map (matching hardware RTL).

  This closes Paper 5 Limitation (vi): the algebraic and hardware-faithful
  definitions are formally equivalent under the scope condition 2^s ≥ q.

  The equivalence means the PF-PINI(2) bound proved algebraically in Paper 5
  applies directly to the hardware computation.
-/
import QanaryPaper6.Basic
import Mathlib.Data.ZMod.Basic

open Finset

variable {q : ℕ} [NeZero q]

/-! ### Nat arithmetic helpers -/

private lemma mod_pow_no_wrap {a b c : ℕ} (hge : c ≤ a) (hac_lt_b : a - c < b) :
    (a + b - c) % b = a - c := by
  have h1 : a + b - c = (a - c) + b := by omega
  rw [h1, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hac_lt_b

private lemma mod_pow_wraparound {a b c : ℕ} (hc_gt_a : a < c) (hc_lt_b : c < b) :
    (a + b - c) % b = a + b - c :=
  Nat.mod_eq_of_lt (by omega)

/-! ### The equivalence theorem -/

/-- **NatEquivalence Bridge Theorem.**

The algebraic Barrett map equals the Nat arithmetic Barrett map
under the scope condition hs : q ≤ 2^s. This bridges the algebraic
proof to the hardware model. The PF-PINI(2) bound from Paper 5
therefore applies to the actual RTL computation. -/
theorem barrett_nat_equivalence (s : ℕ) (hs : q ≤ 2 ^ s)
    (x m : ZMod q) :
    barrettInternalMap s x m = barrettInternalMapNat s hs x m := by
  unfold barrettInternalMap barrettInternalMapNat
  have hx := ZMod.val_lt x
  have hm := ZMod.val_lt m
  split
  · -- Case: m.val ≤ x.val (no wraparound)
    rename_i h_le
    rw [mod_pow_no_wrap h_le (by omega)]
    rw [Nat.mod_eq_of_lt (by omega : x.val - m.val < q)]
    -- Goal: x - m = ↑(x.val - m.val)
    rw [Nat.cast_sub h_le, ZMod.natCast_zmod_val x, ZMod.natCast_zmod_val m]
  · -- Case: m.val > x.val (wraparound)
    rename_i h_gt
    simp only [not_le] at h_gt
    rw [mod_pow_wraparound h_gt (by omega)]
    rw [ZMod.natCast_mod]
    -- Goal: x - m + ↑(2 ^ s) = ↑(x.val + 2 ^ s - m.val)
    -- Strategy: show RHS = ↑x.val + ↑(2^s) - ↑m.val, then use natCast_zmod_val
    conv_rhs => rw [Nat.cast_sub (by omega : m.val ≤ x.val + 2 ^ s),
                     Nat.cast_add, ZMod.natCast_zmod_val x]
    -- Goal: x - m + ↑(2 ^ s) = x + ↑(2 ^ s) - ↑m.val
    rw [ZMod.natCast_zmod_val m]
    push_cast
    ring

/-! ### Consequence: PF-PINI(2) applies to hardware model -/

/-- The hardware-faithful Barrett map satisfies PF-PINI(2). -/
theorem barrettNat_pfpini_two (s : ℕ) (hs : q ≤ 2 ^ s) (x v : ZMod q) :
    (univ.filter (fun m : ZMod q =>
      barrettInternalMapNat s hs x m = v)).card ≤ 2 := by
  -- Rewrite filter predicate using the equivalence
  have : (univ.filter (fun m : ZMod q => barrettInternalMapNat s hs x m = v)) =
         (univ.filter (fun m : ZMod q => barrettInternalMap s x m = v)) := by
    ext m
    simp only [mem_filter, mem_univ, true_and]
    rw [barrett_nat_equivalence s hs x m]
  rw [this]
  exact barrett_max_multiplicity_two s x v
