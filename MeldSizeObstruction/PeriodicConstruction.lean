module

public import MeldSizeObstruction.SparseEyes

/-!
# Periodic sparse full-sided waits for every meld size

Select a sequence beginning at `s` when `(s - 1) % k` is even. This links
every odd residue to its left eye and every even residue to its right eye,
including when the meld size is odd. The exact count of sequences is
`((ranks-k)/k) * ((k+1)/2) + ((ranks-k)%k+1)/2`.
-/

set_option autoImplicit false

@[expose] public section

namespace MeldSizeObstruction

/-- Sequence starts selected periodically by the preceding rank's residue. -/
def periodicStarts (k ranks : ℕ) : Finset ℕ :=
  ((Finset.range (ranks - k)).filter (fun t => t % k % 2 = 0)).image (· + 1)

private theorem periodic_start_mem {k ranks t : ℕ}
    (hlt : t < ranks - k) (heven : t % k % 2 = 0) :
    t + 1 ∈ periodicStarts k ranks :=
  Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, heven⟩, rfl⟩

private theorem periodic_transfers {k ranks : ℕ} (hk : 0 < k) (hkr : k ≤ ranks) :
    ∀ draw < ranks, ∃ eye ∈ sparseEyes k ranks, ∃ rest, Melds k rest ∧
      sequenceHand k (periodicStarts k ranks) + {draw} = {eye} + rest := by
  intro draw hdraw
  by_cases hodd : draw % k % 2 = 1
  · have heye : draw % k ∈ sparseEyes k ranks := by
      exact Finset.mem_image.mpr ⟨draw % k, Finset.mem_range.mpr (Nat.mod_lt _ hk),
        by simp [sparseEye, hodd]⟩
    obtain ⟨rest, hm, hmove⟩ := sequenceTransfer_right hk (periodicStarts k ranks)
      (draw % k) (draw / k) (by
        intro i hi
        have hpos : 1 ≤ draw % k := by omega
        have hstart : draw % k + i * k = (draw % k - 1 + i * k) + 1 := by omega
        rw [hstart]
        apply periodic_start_mem
        · have hmul := Nat.mul_le_mul_right k (show i + 1 ≤ draw / k by omega)
          have hdiv := Nat.mod_add_div draw k
          have hsub := Nat.sub_add_cancel hkr
          have hpred : draw % k - 1 + 1 = draw % k := by omega
          nlinarith
        · have hsmall : draw % k - 1 < k := by have := Nat.mod_lt draw hk; omega
          simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsmall]
          omega)
    refine ⟨draw % k, heye, rest, hm, ?_⟩
    have hend : draw % k + draw / k * k = draw := by
      simpa [Nat.mul_comm] using Nat.mod_add_div draw k
    simpa only [hend] using hmove
  · have heven : draw % k % 2 = 0 := by omega
    let n := (ranks - 1 - draw) / k
    let eye := draw + n * k
    have heye_eq : sparseEye k ranks (draw % k) = eye :=
      sparseEye_of_even_residue hk hdraw heven
    have heye : eye ∈ sparseEyes k ranks :=
      Finset.mem_image.mpr ⟨draw % k, Finset.mem_range.mpr (Nat.mod_lt _ hk), heye_eq⟩
    have heyelt : eye < ranks := by
      rw [← heye_eq]
      exact sparseEye_lt ((Nat.mod_le draw k).trans_lt hdraw)
    obtain ⟨rest, hm, hmove⟩ := sequenceTransfer_left hk (periodicStarts k ranks)
      draw n (by
        intro i hi
        apply periodic_start_mem
        · have hmul := Nat.mul_le_mul_right k (show i + 1 ≤ n by omega)
          have hsub := Nat.sub_add_cancel hkr
          dsimp only [eye] at heyelt
          nlinarith
        · simpa only [Nat.add_mul_mod_self_right] using heven)
    exact ⟨eye, heye, rest, hm, hmove⟩

/-- A sparse wait using left and right eyes and periodically selected sequences. -/
def periodicHand (k q ranks : ℕ) : Multiset ℕ :=
  eyeBlocks k q (sparseEyes k ranks) + sequenceHand k (periodicStarts k ranks)

/-- The periodic construction gives a full-sided wait for every meld size. -/
theorem fullWait_periodic {k ranks : ℕ} (q : ℕ) (hk : 2 ≤ k) (hkr : k ≤ ranks) :
    FullWait k (1 + k * q) ranks (periodicHand k q ranks) := by
  apply fullWait_of_transfers
  · intro eye heye
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp heye
    exact sparseEye_lt ((Finset.mem_range.mp hr).trans_le hkr)
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    omega
  · exact periodic_transfers (by omega) hkr

private theorem sum_even_range (n : ℕ) :
    (∑ i ∈ Finset.range n, if i % 2 = 0 then 1 else 0) = (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

private theorem periodic_block_sum (k n b : ℕ) (hb : b ≤ k) :
    (∑ i ∈ Finset.range b, if (n * k + i) % k % 2 = 0 then 1 else 0) =
      (b + 1) / 2 := by
  calc
    _ = ∑ i ∈ Finset.range b, if i % 2 = 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hsmall : i < k := (Finset.mem_range.mp hi).trans_le hb
      simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hsmall]
    _ = _ := sum_even_range b

private theorem periodic_blocks_sum (k n : ℕ) :
    (∑ i ∈ Finset.range (n * k), if i % k % 2 = 0 then 1 else 0) =
      n * ((k + 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, periodic_block_sum k n k le_rfl,
      Nat.succ_mul]

/-- The periodically selected sequence starts have an explicit closed count. -/
theorem card_periodicStarts {k : ℕ} (hk : 0 < k) (ranks : ℕ) :
    (periodicStarts k ranks).card =
      ((ranks - k) / k) * ((k + 1) / 2) + ((ranks - k) % k + 1) / 2 := by
  rw [periodicStarts, Finset.card_image_of_injective _ (by
    intro i j hij
    exact Nat.add_right_cancel hij), Finset.card_filter]
  have hlen : (ranks - k) / k * k + (ranks - k) % k = ranks - k := by
    simpa [Nat.mul_comm] using Nat.div_add_mod (ranks - k) k
  have hsplit := Finset.sum_range_add
    (fun i => if i % k % 2 = 0 then 1 else 0) ((ranks - k) / k * k) ((ranks - k) % k)
  rw [hlen] at hsplit
  rw [hsplit, periodic_blocks_sum,
    periodic_block_sum k _ _ (Nat.le_of_lt (Nat.mod_lt _ hk))]

/-- The exact winning meld count for the periodic construction. -/
def periodicMeldCount (k q ranks : ℕ) : ℕ :=
  q * (k - 1) + ((ranks - k) / k) * ((k + 1) / 2) + ((ranks - k) % k + 1) / 2

/-- For even meld sizes the periodic count reduces to the alternating bound. -/
theorem periodicMeldCount_even (k q ranks : ℕ) (hkeven : k % 2 = 0) :
    periodicMeldCount k q ranks = q * (k - 1) + (ranks - k + 1) / 2 := by
  have hhalf : (k + 1) / 2 = k / 2 := by omega
  have hk : 2 * (k / 2) = k := by omega
  have hprod := congrArg (fun x => ((ranks - k) / k) * x) hk
  have hlen : ranks - k + 1 = ((ranks - k) % k + 1) +
      2 * (((ranks - k) / k) * (k / 2)) := by
    have := Nat.div_add_mod (ranks - k) k
    nlinarith
  dsimp only [periodicMeldCount]
  rw [hhalf, hlen, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
  omega

/-- The hand size fixes every winning decomposition's meld count. -/
theorem periodicHand_card {k : ℕ} (q ranks : ℕ) (hk : 2 ≤ k) :
    (periodicHand k q ranks).card + 1 = (1 + k * q) + k * periodicMeldCount k q ranks := by
  rw [periodicHand, card_eyeBlocks_add_sequenceHand, card_sparseEyes,
    card_periodicStarts (by omega)]
  have hpred : k - 1 + 1 = k := by omega
  have hprod := congrArg (fun x => k * q * x) hpred
  dsimp only [periodicMeldCount]
  nlinarith

/-- A concrete full-sided wait at the exact closed-form meld count. -/
theorem exists_fullWait_periodic {k ranks : ℕ} (q : ℕ) (hk : 2 ≤ k) (hkr : k ≤ ranks) :
    ∃ h : Multiset ℕ, FullWait k (1 + k * q) ranks h ∧
      h.card + 1 = (1 + k * q) + k * periodicMeldCount k q ranks :=
  ⟨periodicHand k q ranks, fullWait_periodic q hk hkr, periodicHand_card q ranks hk⟩

end MeldSizeObstruction
