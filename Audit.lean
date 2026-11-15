module

import MeldSizeObstruction

#print axioms MeldSizeObstruction.draw_eye_rigidity
#print axioms MeldSizeObstruction.residue_compatible_iff

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
