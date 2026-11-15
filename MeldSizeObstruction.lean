module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Choose

/-!
# Rigidity of the draw-eye residue equations

The algebraic core of the larger-meld obstruction: with at least four
coordinates, translating and scaling the coordinate vectors cannot preserve
their classes modulo constant vectors, unless the scale is one.
-/

set_option autoImplicit false

@[expose] public section

namespace MeldSizeObstruction

universe u

variable {k : ℕ} {R : Type u} [CommRing R] [Nontrivial R]

/-- One tile in a specified rank-residue class. -/
def pointMass (i r : Fin k) : R := if r = i then 1 else 0

private lemma exists_outside (s : Finset (Fin k)) (hs : s.card < k) :
    ∃ r, r ∉ s := by
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show s.card < (Finset.univ : Finset (Fin k)).card by simpa using hs)
  exact ⟨r, hr⟩

private lemma sparse_difference_zero
    (hone : (1 : R) ≠ -1) {i j r s : Fin k} (hrs : r ≠ s)
    (h : pointMass (R := R) i r - pointMass j r = pointMass i s - pointMass j s) :
    pointMass i r - pointMass j r = (0 : R) := by
  classical
  unfold pointMass at *
  split_ifs at h ⊢ <;> simp_all

private lemma diagonal_difference_zero
    (hk : 4 ≤ k) (hone : (1 : R) ≠ -1) {i j u v : Fin k}
    (p t : R)
    (h : ∀ r, pointMass i r - pointMass j r -
      p * (pointMass u r - pointMass v r) = t) :
    t = 0 := by
  classical
  obtain ⟨r, hr⟩ := exists_outside ({u, v} : Finset (Fin k)) (by
    have := (Finset.card_le_two : ({u, v} : Finset (Fin k)).card ≤ 2)
    omega)
  have hr' : r ≠ u ∧ r ≠ v := by simpa using hr
  obtain ⟨s, hs⟩ := exists_outside ({r, u, v} : Finset (Fin k)) (by
    have := (Finset.card_le_three : ({r, u, v} : Finset (Fin k)).card ≤ 3)
    omega)
  have hs' : s ≠ r ∧ s ≠ u ∧ s ≠ v := by simpa using hs
  have hR : pointMass i r - pointMass j r = t := by
    simpa [pointMass, hr'.1, hr'.2] using h r
  have hS : pointMass i s - pointMass j s = t := by
    simpa [pointMass, hs'.2.1, hs'.2.2] using h s
  exact hR.symm.trans (sparse_difference_zero hone hs'.1.symm (hR.trans hS.symm))

/-- The coordinate-vector classes have no nontrivial translation or scalar
symmetry when there are at least four coordinates and `1 ≠ -1`. -/
theorem draw_eye_rigidity
    (hk : 4 ≤ k) (hone : (1 : R) ≠ -1)
    (C : Fin k → R) (p : R) (f : Fin k → Fin k) (a : Fin k → R)
    (h : ∀ i r, C r + pointMass i r - p * pointMass (f i) r = a i) :
    p = 1 ∧ ∀ r s, C r = C s := by
  classical
  have ha : ∀ i j, a i = a j := by
    intro i j
    have hd : ∀ r, pointMass i r - pointMass j r -
        p * (pointMass (f i) r - pointMass (f j) r) = a i - a j := by
      intro r
      linear_combination h i r - h j r
    exact sub_eq_zero.mp (diagonal_difference_zero hk hone p (a i - a j) hd)
  have hd : ∀ i j r, pointMass i r - pointMass j r =
      p * (pointMass (f i) r - pointMass (f j) r) := by
    intro i j r
    linear_combination h i r - h j r + ha i j
  have hf : Function.Injective f := by
    intro i j hfij
    by_contra hij
    have hi := hd i j i
    simp [pointMass, hij, hfij] at hi
  let i : Fin k := ⟨0, by omega⟩
  obtain ⟨j, hj⟩ := exists_outside ({i} : Finset (Fin k)) (by simp; omega)
  have hji : j ≠ i := by simpa using hj
  have hp : p ≠ 0 := by
    intro hp
    have hi := hd i j i
    simp [pointMass, hji.symm, hp] at hi
  have hf_mem : ∀ i j, i ≠ j → f i = i ∨ f i = j := by
    intro i j hij
    by_contra hn
    have hn' : f i ≠ i ∧ f i ≠ j := not_or.mp hn
    have hfi : f i ≠ f j := hf.ne hij
    have hi := hd i j (f i)
    have hz : (0 : R) = p := by
      simpa [pointMass, hn'.1, hn'.2, hfi] using hi
    exact hp hz.symm
  have hf_id : ∀ i, f i = i := by
    intro i
    obtain ⟨j, hj⟩ := exists_outside ({i} : Finset (Fin k)) (by simp; omega)
    have hji : j ≠ i := by simpa using hj
    obtain ⟨l, hl⟩ := exists_outside ({i, j} : Finset (Fin k)) (by
      have := (Finset.card_le_two : ({i, j} : Finset (Fin k)).card ≤ 2)
      omega)
    have hl' : l ≠ i ∧ l ≠ j := by simpa using hl
    rcases hf_mem i j hji.symm with hi | hfj
    · exact hi
    · rcases hf_mem i l hl'.1.symm with hi | hfl
      · exact hi
      · exact False.elim (hl'.2 (hfl.symm.trans hfj))
  have hp1 : p = 1 := by
    have hi := hd i j i
    simpa [pointMass, hf_id, hji.symm] using hi.symm
  refine ⟨hp1, ?_⟩
  intro r s
  have hr := h i r
  have hs := h i s
  simp [hf_id, hp1] at hr hs
  exact hr.trans hs.symm

/-- The residue equations of a full-sided wait with `k`-tile melds force
the eye size to be one modulo `k`, and the class counts to be equal. -/
theorem residue_rigidity
    (hk : 4 ≤ k) (C : Fin k → ZMod k) (p : ZMod k)
    (f : Fin k → Fin k) (a : Fin k → ZMod k)
    (h : ∀ i r, C r + pointMass i r - p * pointMass (f i) r = a i) :
    p = 1 ∧ ∀ r s, C r = C s := by
  have : Fact (1 < k) := ⟨by omega⟩
  have hone : (1 : ZMod k) ≠ -1 := by
    intro hh
    have h2 : (2 : ZMod k) = 0 := by linear_combination hh
    have hv := congrArg ZMod.val h2
    norm_num [ZMod.val_ofNat, Nat.mod_eq_of_lt (show 2 < k by omega)] at hv
  exact draw_eye_rigidity hk hone C p f a h

/-- The necessary modular condition for every draw residue to admit an eye. -/
def ResidueCompatible (C : Fin k → ZMod k) (p : ZMod k) : Prop :=
  ∀ i, ∃ j a, ∀ r, C r + pointMass i r - p * pointMass j r = a

/-- Complete classification of the modular condition, independently of
whether a particular hand has a winning decomposition. -/
theorem residue_compatible_iff (hk : 4 ≤ k) (C : Fin k → ZMod k) (p : ZMod k) :
    ResidueCompatible C p ↔ p = 1 ∧ ∀ r s, C r = C s := by
  constructor
  · intro h
    choose f a ha using h
    exact residue_rigidity hk C p f a ha
  · rintro ⟨hp, hC⟩ i
    refine ⟨i, C i, ?_⟩
    intro r
    simpa [hp] using hC r i

end MeldSizeObstruction
