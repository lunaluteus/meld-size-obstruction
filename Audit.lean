module

import MeldSizeObstruction.Hands
import Mathlib.Tactic.IntervalCases

#print axioms MeldSizeObstruction.draw_eye_rigidity
#print axioms MeldSizeObstruction.residue_compatible_iff
#print axioms MeldSizeObstruction.FullWait.obstruction
#print axioms MeldSizeObstruction.fullWait_uniform
#print axioms MeldSizeObstruction.exists_fullWait_iff

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
