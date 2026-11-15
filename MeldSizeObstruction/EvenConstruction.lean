module

public import MeldSizeObstruction.Construction
public import Mathlib.Tactic.Linarith

/-!
# Full-sided waits with fewer melds for even meld sizes

An alternating family of consecutive melds links every rank to a selected eye
rank in its residue class. This gives a construction with
`q * (k - 1) + (ranks - k + 1) / 2` winning melds and eye size `1 + k*q`.
Tile multiplicities are unrestricted; no minimality claim is made.
-/

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

/-- Consecutive melds starting at alternate interior ranks. -/
def sparseStarts (k ranks : ℕ) : Finset ℕ :=
  (Finset.range ((ranks - k) / 2)).image (fun i => 2 * i + 1)

private theorem mem_sparseStarts {k ranks s : ℕ} :
    s ∈ sparseStarts k ranks ↔ s < ranks - k ∧ s % 2 = 1 := by
  constructor
  · intro hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    have hi' := Finset.mem_range.mp hi
    omega
  · rintro ⟨hlt, hodd⟩
    exact Finset.mem_image.mpr ⟨s / 2, Finset.mem_range.mpr (by omega), by omega⟩

private theorem sparseEye_mod {k ranks r : ℕ} (hr : r < k) :
    sparseEye k ranks r % k = r := by
  unfold sparseEye
  split_ifs <;> simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

private theorem sparseEye_lt {k ranks r : ℕ} (hr : r < ranks) :
    sparseEye k ranks r < ranks := by
  unfold sparseEye
  split_ifs
  · exact hr
  · have := Nat.mul_div_le (ranks - 1 - r) k
    omega

private theorem sparseEye_even {k ranks r : ℕ} (hk : k % 2 = 0) (hr : r % 2 = 0) :
    sparseEye k ranks r % 2 = 0 := by
  simp [sparseEye, hr, Nat.add_mod, Nat.mul_mod, hk]

/-- The eye set has exactly one rank in every residue class. -/
theorem card_sparseEyes (k ranks : ℕ) : (sparseEyes k ranks).card = k := by
  rw [sparseEyes, Finset.card_image_iff.mpr]
  · exact Finset.card_range k
  · intro a ha b hb hab
    have hmod := congrArg (· % k) hab
    simpa only [sparseEye_mod (Finset.mem_range.mp ha),
      sparseEye_mod (Finset.mem_range.mp hb)] using hmod

/-- The alternating sequence family has half as many members as spare ranks. -/
theorem card_sparseStarts (k ranks : ℕ) :
    (sparseStarts k ranks).card = (ranks - k) / 2 := by
  rw [sparseStarts, Finset.card_image_of_injective _ (by
    intro i j hij
    change 2 * i + 1 = 2 * j + 1 at hij
    omega), Finset.card_range]

private theorem sparseEye_of_even_draw {k ranks draw : ℕ} (hk : 0 < k)
    (hkeven : k % 2 = 0) (hdraw : draw < ranks) (hdeven : draw % 2 = 0) :
    sparseEye k ranks (draw % k) = draw + ((ranks - 1 - draw) / k) * k := by
  have hres : draw % k % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd draw (Nat.dvd_of_mod_eq_zero hkeven)]
    exact hdeven
  have hsub : ranks - 1 - draw % k = (ranks - 1 - draw) + k * (draw / k) := by
    have := Nat.mod_add_div draw k
    omega
  simp only [sparseEye, hres, Nat.zero_ne_one, ↓reduceIte, hsub,
    Nat.add_mul_div_left _ _ hk]
  have := Nat.mod_add_div draw k
  nlinarith

private theorem sparse_transfers {k ranks : ℕ} (hk : 0 < k)
    (hkeven : k % 2 = 0) (hreven : ranks % 2 = 0) (hkr : k ≤ ranks) :
    ∀ draw < ranks, ∃ eye ∈ sparseEyes k ranks, ∃ rest, Melds k rest ∧
      sequenceHand k (sparseStarts k ranks) + {draw} = {eye} + rest := by
  intro draw hdraw
  by_cases hodd : draw % 2 = 1
  · have hres : draw % k % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd draw (Nat.dvd_of_mod_eq_zero hkeven)]
      exact hodd
    have heye : draw % k ∈ sparseEyes k ranks := by
      apply Finset.mem_image.mpr
      refine ⟨draw % k, Finset.mem_range.mpr (Nat.mod_lt _ hk), ?_⟩
      simp [sparseEye, hres]
    obtain ⟨rest, hm, hmove⟩ := sequenceTransfer_right hk (sparseStarts k ranks)
      (draw % k) (draw / k) (by
        intro i hi
        apply mem_sparseStarts.mpr
        constructor
        · have hmul := Nat.mul_le_mul_right k (show i + 1 ≤ draw / k by omega)
          have hdiv := Nat.mod_add_div draw k
          have hsub := Nat.sub_add_cancel hkr
          nlinarith
        · simp [Nat.add_mod, Nat.mul_mod, hkeven, hres])
    refine ⟨draw % k, heye, rest, hm, ?_⟩
    have hend : draw % k + draw / k * k = draw := by
      simpa [Nat.mul_comm] using Nat.mod_add_div draw k
    simpa only [hend] using hmove
  · have hdeven : draw % 2 = 0 := by omega
    let n := (ranks - 1 - draw) / k
    let eye := draw + n * k
    have heye_eq : sparseEye k ranks (draw % k) = eye :=
      sparseEye_of_even_draw hk hkeven hdraw hdeven
    have heye : eye ∈ sparseEyes k ranks :=
      Finset.mem_image.mpr ⟨draw % k, Finset.mem_range.mpr (Nat.mod_lt _ hk), heye_eq⟩
    have heyelt : eye < ranks := by
      rw [← heye_eq]
      exact sparseEye_lt ((Nat.mod_le draw k).trans_lt hdraw)
    have heyeeven : eye % 2 = 0 := by
      simp [eye, Nat.add_mod, Nat.mul_mod, hdeven, hkeven]
    have heyeend : eye + 1 < ranks := by omega
    obtain ⟨rest, hm, hmove⟩ := sequenceTransfer_left hk (sparseStarts k ranks)
      draw n (by
        intro i hi
        apply mem_sparseStarts.mpr
        constructor
        · have hmul := Nat.mul_le_mul_right k (show i + 1 ≤ n by omega)
          dsimp only [eye] at heyeend
          have hsub := Nat.sub_add_cancel hkr
          nlinarith
        · simp [Nat.add_mod, Nat.mul_mod, hkeven, hdeven])
    exact ⟨eye, heye, rest, hm, hmove⟩

/-- The alternating construction, padded to an even number of ranks when needed. -/
def sparseHand (k q ranks : ℕ) : Multiset ℕ :=
  eyeBlocks k q (sparseEyes k (ranks + ranks % 2)) +
    sequenceHand k (sparseStarts k (ranks + ranks % 2))

/-- Every even meld size admits the sparse construction for every suit length. -/
theorem fullWait_sparse {k ranks : ℕ} (q : ℕ) (hk : 2 ≤ k)
    (hkeven : k % 2 = 0) (hkr : k ≤ ranks) :
    FullWait k (1 + k * q) ranks (sparseHand k q ranks) := by
  let padded := ranks + ranks % 2
  have hpadded : padded % 2 = 0 := by dsimp [padded]; omega
  have hpadle : ranks ≤ padded := by dsimp [padded]; omega
  have hpadlt : padded ≤ ranks + 1 := by dsimp [padded]; omega
  have hkp : k ≤ padded := hkr.trans hpadle
  apply fullWait_of_transfers
  · intro eye heye
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp heye
    change sparseEye k padded r < ranks
    have hrk := Finset.mem_range.mp hr
    have hrr : r < ranks := hrk.trans_le hkr
    by_cases hodd : r % 2 = 1
    · simpa [sparseEye, hodd] using hrr
    · have hreven : r % 2 = 0 := by omega
      have hlt := sparseEye_lt (k := k) (hrr.trans_le hpadle)
      have heven := sparseEye_even (ranks := padded) hkeven hreven
      have : sparseEye k padded r + 1 < padded := by omega
      omega
  · intro s hs
    obtain ⟨hslt, _⟩ := mem_sparseStarts.mp hs
    have hsub := Nat.sub_add_cancel hkp
    omega
  · intro draw hdraw
    exact sparse_transfers (by omega) hkeven hpadded hkp draw (hdraw.trans_le hpadle)

/-- The sparse wait uses exactly the advertised number of melds after any draw. -/
theorem sparseHand_card {k ranks : ℕ} (q : ℕ) (hk : 2 ≤ k)
    (hkeven : k % 2 = 0) (hkr : k ≤ ranks) :
    (sparseHand k q ranks).card + 1 =
      (1 + k * q) + k * (q * (k - 1) + (ranks - k + 1) / 2) := by
  rw [sparseHand, card_eyeBlocks_add_sequenceHand, card_sparseEyes,
    card_sparseStarts]
  have hdiv : (ranks + ranks % 2 - k) / 2 = (ranks - k + 1) / 2 := by omega
  rw [hdiv]
  have hpred : k - 1 + 1 = k := by omega
  have hprod := congrArg (fun x => k * q * x) hpred
  nlinarith

/-- An explicit existence bound, with the hand's exact size rather than only residues. -/
theorem exists_fullWait_even {k ranks : ℕ} (q : ℕ) (hk : 2 ≤ k)
    (hkeven : k % 2 = 0) (hkr : k ≤ ranks) :
    ∃ h : Multiset ℕ, FullWait k (1 + k * q) ranks h ∧
      h.card + 1 = (1 + k * q) + k * (q * (k - 1) + (ranks - k + 1) / 2) :=
  ⟨sparseHand k q ranks, fullWait_sparse q hk hkeven hkr,
    sparseHand_card q hk hkeven hkr⟩

end MeldSizeObstruction
