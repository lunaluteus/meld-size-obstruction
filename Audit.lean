module

import MeldSizeObstruction.Hands
import MeldSizeObstruction.EvenConstruction
import MeldSizeObstruction.PeriodicConstruction
import MeldSizeObstruction.LowerBounds
import Mathlib.Tactic.IntervalCases

#print axioms MeldSizeObstruction.draw_eye_rigidity
#print axioms MeldSizeObstruction.residue_compatible_iff
#print axioms MeldSizeObstruction.FullWait.obstruction
#print axioms MeldSizeObstruction.fullWait_uniform
#print axioms MeldSizeObstruction.exists_fullWait_iff
#print axioms MeldSizeObstruction.fullWait_sparse
#print axioms MeldSizeObstruction.exists_fullWait_even
#print axioms MeldSizeObstruction.fullWait_periodic
#print axioms MeldSizeObstruction.exists_fullWait_periodic
#print axioms MeldSizeObstruction.FullWait.meld_count_lower
#print axioms MeldSizeObstruction.FullWait.meld_count_strict_lower
#print axioms MeldSizeObstruction.minimum_meld_count_short
#print axioms MeldSizeObstruction.FullWait.meld_count_lower_of_three_extra_ranks
#print axioms MeldSizeObstruction.minimum_meld_count_three_or_four_extra

open MeldSizeObstruction

example (C : Fin 4 → ZMod 4) : ¬ ResidueCompatible C 3 := by
  intro h
  have hp := ((residue_compatible_iff (by decide) C 3).mp h).1
  exact (by decide : (3 : ZMod 4) ≠ 1) hp

example (C : Fin 5 → ZMod 5) : ¬ ResidueCompatible C 2 := by
  intro h
  have hp := ((residue_compatible_iff (by decide) C 2).mp h).1
  exact (by decide : (2 : ZMod 5) ≠ 1) hp

/-- Three coordinates really do permit an exceptional eye residue. -/
example : ResidueCompatible (fun r : Fin 3 => if r = 1 then 1 else 0) 2 := by
  intro i
  refine ⟨2 - i, if i = 1 then 0 else 1, ?_⟩
  fin_cases i <;> decide

/-- In characteristic two, the four-coordinate conclusion need not hold. -/
example : ∃ (C : Fin 4 → ZMod 2) (f : Fin 4 → Fin 4) (a : Fin 4 → ZMod 2),
    (∀ i r, C r + pointMass i r - pointMass (f i) r = a i) ∧ C 0 ≠ C 2 := by
  refine ⟨(fun r => if r.val < 2 then 1 else 0),
    (fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 3 else 2),
    (fun i => if i.val < 2 then 0 else 1), ?_⟩
  decide

example (h : Multiset ℕ) : ¬ FullWait 4 3 8 h :=
  not_fullWait_pred (by decide) (by decide) h

example (h : Multiset ℕ) : ¬ FullWait 5 2 9 h :=
  not_fullWait_pair (by decide) (by decide) h

/-- A five-tile eye and four-tile melds admit an actual six-rank full wait. -/
example : FullWait 4 5 6 (uniformHand 4 1 6) :=
  fullWait_uniform 4 1 (by decide)

/-- The sparse construction needs only four melds over these six ranks. -/
example : FullWait 4 5 6 (sparseHand 4 1 6) ∧
    (sparseHand 4 1 6).card + 1 = 5 + 4 * 4 :=
  ⟨fullWait_sparse 1 (by decide) (by decide) (by decide), by decide⟩

/-- Padding for an odd suit length leaves all tiles inside the original suit. -/
example : ∃ h : Multiset ℕ, FullWait 4 5 13 h ∧ h.card + 1 = 5 + 4 * 8 := by
  exact exists_fullWait_even 1 (by decide) (by decide) (by decide)

/-- The empty hand works when the eye is a single tile and ranks equal meld size. -/
example : FullWait 4 1 4 (sparseHand 4 0 4) ∧ (sparseHand 4 0 4).card = 0 :=
  ⟨fullWait_sparse 0 (by decide) (by decide) (by decide), by decide⟩

/-- The construction also works at the smallest even meld size. -/
example : ∃ h : Multiset ℕ, FullWait 2 5 7 h ∧ h.card + 1 = 5 + 2 * 5 := by
  exact exists_fullWait_even 2 (by decide) (by decide) (by decide)

/-- The advertised four-tile formula holds for arbitrary suit lengths. -/
example (ranks : ℕ) (hranks : 4 ≤ ranks) :
    ∃ h : Multiset ℕ, FullWait 4 5 ranks h ∧
      h.card + 1 = 5 + 4 * ((ranks + 1) / 2 + 1) := by
  obtain ⟨h, hw, hc⟩ := exists_fullWait_even 1 (by decide) (by decide) hranks
  exact ⟨h, hw, by omega⟩

/-- Odd meld sizes admit the same endpoint-transfer construction. -/
example : FullWait 5 6 9 (periodicHand 5 1 9) ∧
    (periodicHand 5 1 9).card + 1 = 6 + 5 * 6 :=
  ⟨fullWait_periodic 1 (by decide) (by decide), by decide⟩

/-- A longer odd-meld example exercises complete blocks and a partial block. -/
example : ∃ h : Multiset ℕ, FullWait 5 6 16 h ∧ h.card + 1 = 6 + 5 * 11 := by
  exact exists_fullWait_periodic 1 (by decide) (by decide)

/-- Three-tile melds also permit this construction with a four-tile eye. -/
example : ∃ h : Multiset ℕ, FullWait 3 4 9 h ∧ h.card + 1 = 4 + 3 * 6 := by
  exact exists_fullWait_periodic 1 (by decide) (by decide)

/-- A sparse construction's count is only an existence bound: q=0 needs no melds. -/
example (k ranks : ℕ) : FullWait k 1 ranks 0 := fullWait_single_eye k ranks

/-- Four-tile melds and a five-tile eye need at least four melds on six ranks. -/
example (h : Multiset ℕ) (m : ℕ) (hw : FullWait 4 5 6 h)
    (hc : h.card + 1 = 5 + 4 * m) : 4 ≤ m :=
  hw.meld_count_strict_lower (q := 1) (by decide) (by decide) (by decide) hc

/-- The exact short-suit minimum also holds for arbitrary positive eye quotients. -/
example (k q : ℕ) (hk : 4 ≤ k) (hq : 0 < q) :
    (∃ h : Multiset ℕ, FullWait k (1 + k * q) (k + 2) h ∧
      h.card + 1 = (1 + k * q) + k * (q * (k - 1) + 1)) ∧
    ∀ (h : Multiset ℕ) (m : ℕ), FullWait k (1 + k * q) (k + 2) h →
      h.card + 1 = (1 + k * q) + k * m → q * (k - 1) + 1 ≤ m := by
  simpa using minimum_meld_count_short (k := k) (q := q) (ranks := k + 2)
    hk hq (by omega) le_rfl

/-- With exactly k ranks the capacity bound itself is attained. -/
example (k q : ℕ) (hk : 4 ≤ k) (hq : 0 < q) :
    (∃ h : Multiset ℕ, FullWait k (1 + k * q) k h ∧
      h.card + 1 = (1 + k * q) + k * (q * (k - 1))) ∧
    ∀ (h : Multiset ℕ) (m : ℕ), FullWait k (1 + k * q) k h →
      h.card + 1 = (1 + k * q) + k * m → q * (k - 1) ≤ m := by
  simpa using minimum_meld_count_short (k := k) (q := q) (ranks := k)
    hk hq le_rfl (by omega)

/-- Four extra ranks attain the sharper bound even when the suit has length `2*k`. -/
example : (∃ h : Multiset ℕ, FullWait 4 5 8 h ∧ h.card + 1 = 5 + 4 * 5) ∧
    ∀ (h : Multiset ℕ) (m : ℕ), FullWait 4 5 8 h → h.card + 1 = 5 + 4 * m → 5 ≤ m :=
  minimum_meld_count_three_or_four_extra (k := 4) (q := 1) (extra := 4)
    (by decide) (by decide) (by decide) (by decide)

/-- With only one drawable residue, the eye obstruction no longer applies. -/
example : FullWait 4 2 1 (Multiset.replicate 5 0) := by
  constructor
  · intro tile htile
    have := Multiset.eq_of_mem_replicate htile
    omega
  · intro tile ht
    have hzero : tile = 0 := by omega
    subst tile
    refine ⟨0, Multiset.replicate 4 0, ?_, ?_⟩
    · simpa using Melds.identical 0 (Melds.empty : Melds 4 0)
    · decide

/-- Ordinary Nine Gates, with ranks numbered from zero. -/
private def nineGates : Multiset ℕ :=
  {0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 8}

/-- Each of the nine draws has a literal four-meld-and-pair certificate. -/
example : FullWait 3 2 9 nineGates := by
  constructor
  · intro tile htile
    simp [nineGates] at htile
    omega
  · intro tile ht
    interval_cases tile
    · refine ⟨8, _, Melds.identical 0 (Melds.consecutive 0 (
        Melds.consecutive 3 (Melds.consecutive 6 Melds.empty))), ?_⟩
      decide
    · refine ⟨1, _, Melds.identical 0 (Melds.consecutive 2 (
        Melds.consecutive 5 (Melds.identical 8 Melds.empty))), ?_⟩
      decide
    · refine ⟨0, _, Melds.consecutive 0 (Melds.consecutive 2 (
        Melds.consecutive 5 (Melds.identical 8 Melds.empty))), ?_⟩
      decide
    · refine ⟨8, _, Melds.identical 0 (Melds.consecutive 1 (
        Melds.consecutive 3 (Melds.consecutive 6 Melds.empty))), ?_⟩
      decide
    · refine ⟨4, _, Melds.identical 0 (Melds.consecutive 1 (
        Melds.consecutive 5 (Melds.identical 8 Melds.empty))), ?_⟩
      decide
    · refine ⟨0, _, Melds.consecutive 0 (Melds.consecutive 3 (
        Melds.consecutive 5 (Melds.identical 8 Melds.empty))), ?_⟩
      decide
    · refine ⟨8, _, Melds.identical 0 (Melds.consecutive 1 (
        Melds.consecutive 4 (Melds.consecutive 6 Melds.empty))), ?_⟩
      decide
    · refine ⟨7, _, Melds.identical 0 (Melds.consecutive 1 (
        Melds.consecutive 4 (Melds.identical 8 Melds.empty))), ?_⟩
      decide
    · refine ⟨0, _, Melds.consecutive 0 (Melds.consecutive 3 (
        Melds.consecutive 6 (Melds.identical 8 Melds.empty))), ?_⟩
      decide
