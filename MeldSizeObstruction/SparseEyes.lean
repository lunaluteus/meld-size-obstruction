module

public import MeldSizeObstruction.Construction
public import Mathlib.Tactic.Linarith

/-! # Left and right eye ranks for sparse full-sided waits -/

set_option autoImplicit false

@[expose] public section

namespace MeldSizeObstruction

/-- Odd residues use a left eye; even residues use the rightmost available eye. -/
def sparseEye (k ranks residue : ℕ) : ℕ :=
  if residue % 2 = 1 then residue
  else residue + k * ((ranks - 1 - residue) / k)

/-- One eye rank for each rank residue. -/
def sparseEyes (k ranks : ℕ) : Finset ℕ :=
  (Finset.range k).image (sparseEye k ranks)

/-- An eye rank remains in the residue class it represents. -/
theorem sparseEye_mod {k ranks r : ℕ} (hr : r < k) :
    sparseEye k ranks r % k = r := by
  unfold sparseEye
  split_ifs <;> simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

/-- Every selected eye stays within the suit. -/
theorem sparseEye_lt {k ranks r : ℕ} (hr : r < ranks) :
    sparseEye k ranks r < ranks := by
  unfold sparseEye
  split_ifs
  · exact hr
  · have := Nat.mul_div_le (ranks - 1 - r) k
    omega

/-- The eye set has exactly one rank in every residue class. -/
theorem card_sparseEyes (k ranks : ℕ) : (sparseEyes k ranks).card = k := by
  rw [sparseEyes, Finset.card_image_iff.mpr]
  · exact Finset.card_range k
  · intro a ha b hb hab
    have hmod := congrArg (· % k) hab
    simpa only [sparseEye_mod (Finset.mem_range.mp ha),
      sparseEye_mod (Finset.mem_range.mp hb)] using hmod

/-- A draw in an even residue reaches its eye by a whole number of `k`-steps. -/
theorem sparseEye_of_even_residue {k ranks draw : ℕ} (hk : 0 < k)
    (hdraw : draw < ranks) (hres : draw % k % 2 = 0) :
    sparseEye k ranks (draw % k) = draw + ((ranks - 1 - draw) / k) * k := by
  have hsub : ranks - 1 - draw % k = (ranks - 1 - draw) + k * (draw / k) := by
    have := Nat.mod_add_div draw k
    omega
  simp only [sparseEye, hres, Nat.zero_ne_one, ↓reduceIte, hsub,
    Nat.add_mul_div_left _ _ hk]
  have := Nat.mod_add_div draw k
  nlinarith

end MeldSizeObstruction
