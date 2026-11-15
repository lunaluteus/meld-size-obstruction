module

public import MeldSizeObstruction.Hands

/-!
# Sparse constructions of full-sided waits

Shifting a consecutive meld by one rank transfers a single tile between
its endpoints. A chain of such shifts gives explicit winning decompositions.
-/

set_option autoImplicit false

@[expose] public section

namespace MeldSizeObstruction

/-- One consecutive meld at each selected starting rank. -/
def sequenceHand (k : ℕ) (starts : Finset ℕ) : Multiset ℕ :=
  ∑ s ∈ starts, Multiset.Ico s (s + k)

/-- A family of consecutive melds is meldable. -/
theorem Melds.sequenceHand (k : ℕ) (starts : Finset ℕ) :
    Melds k (sequenceHand k starts) :=
  Melds.sum starts _ fun s _ => by
    simpa using Melds.consecutive s (Melds.empty : Melds k 0)

/-- Shifting a consecutive meld transfers one tile between its endpoints. -/
theorem consecutive_shift (k a : ℕ) :
    Multiset.Ico a (a + k) + {a + k} =
      {a} + Multiset.Ico (a + 1) (a + 1 + k) := by
  have singleton (x : ℕ) : Multiset.Ico x (x + 1) = {x} := by
    change (Finset.Ico x (x + 1)).val = _
    rw [Nat.Ico_succ_singleton]
    rfl
  have hleft := Multiset.Ico_add_Ico_eq_Ico
    (show a ≤ a + k by omega) (show a + k ≤ a + k + 1 by omega)
  have hright := Multiset.Ico_add_Ico_eq_Ico
    (show a ≤ a + 1 by omega) (show a + 1 ≤ a + k + 1 by omega)
  rw [singleton] at hleft hright
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hleft.trans hright.symm

/-- Consecutive endpoint transfers telescope along a residue class. -/
theorem sequence_chain_shift (k a n : ℕ) :
    (∑ i ∈ Finset.range n, Multiset.Ico (a + i * k) (a + i * k + k)) +
        {a + n * k} =
      {a} + ∑ i ∈ Finset.range n,
        Multiset.Ico (a + i * k + 1) (a + i * k + 1 + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    have hend : a + (n + 1) * k = a + n * k + k := by
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [hend, add_assoc, consecutive_shift]
    rw [← add_assoc, ih, add_assoc]

private theorem chain_injective {k : ℕ} (hk : 0 < k) (a : ℕ) :
    Function.Injective (fun i : ℕ => a + i * k) := by
  intro i j hij
  apply Nat.mul_left_cancel hk
  simpa only [Nat.mul_comm] using Nat.add_left_cancel hij

/-- A chain contained in the starting ranks permits a rightward endpoint transfer. -/
theorem sequenceTransfer_right {k : ℕ} (hk : 0 < k) (starts : Finset ℕ) (a n : ℕ)
    (hchain : ∀ i < n, a + i * k ∈ starts) :
    ∃ rest, Melds k rest ∧
      sequenceHand k starts + {a + n * k} = {a} + rest := by
  let path := (Finset.range n).image (fun i => a + i * k)
  have hsubset : path ⊆ starts := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    exact hchain i (Finset.mem_range.mp hi)
  have hpath : sequenceHand k path =
      ∑ i ∈ Finset.range n, Multiset.Ico (a + i * k) (a + i * k + k) := by
    exact Finset.sum_image (fun i _ j _ h => chain_injective hk a h)
  have hsplit : sequenceHand k starts = sequenceHand k (starts \ path) +
      ∑ i ∈ Finset.range n, Multiset.Ico (a + i * k) (a + i * k + k) := by
    rw [← hpath]
    exact (Finset.sum_sdiff hsubset).symm
  let shifted := ∑ i ∈ Finset.range n,
    Multiset.Ico (a + i * k + 1) (a + i * k + 1 + k)
  refine ⟨sequenceHand k (starts \ path) + shifted, ?_, ?_⟩
  · exact (Melds.sequenceHand k _).add (Melds.sum _ _ fun i _ => by
      simpa using Melds.consecutive (a + i * k + 1) (Melds.empty : Melds k 0))
  · rw [hsplit, add_assoc, sequence_chain_shift]
    dsimp only [shifted]
    ac_rfl

/-- The same shifts in reverse permit a leftward endpoint transfer. -/
theorem sequenceTransfer_left {k : ℕ} (hk : 0 < k) (starts : Finset ℕ) (a n : ℕ)
    (hchain : ∀ i < n, a + i * k + 1 ∈ starts) :
    ∃ rest, Melds k rest ∧
      sequenceHand k starts + {a} = {a + n * k} + rest := by
  let path := (Finset.range n).image (fun i => a + i * k + 1)
  have hsubset : path ⊆ starts := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    exact hchain i (Finset.mem_range.mp hi)
  have hpath : sequenceHand k path =
      ∑ i ∈ Finset.range n,
        Multiset.Ico (a + i * k + 1) (a + i * k + 1 + k) := by
    apply Finset.sum_image
    intro i _ j _ hij
    change a + i * k + 1 = a + j * k + 1 at hij
    exact chain_injective hk a (Nat.add_right_cancel hij)
  have hsplit : sequenceHand k starts = sequenceHand k (starts \ path) +
      ∑ i ∈ Finset.range n,
        Multiset.Ico (a + i * k + 1) (a + i * k + 1 + k) := by
    rw [← hpath]
    exact (Finset.sum_sdiff hsubset).symm
  let shifted := ∑ i ∈ Finset.range n,
    Multiset.Ico (a + i * k) (a + i * k + k)
  refine ⟨sequenceHand k (starts \ path) + shifted, ?_, ?_⟩
  · exact (Melds.sequenceHand k _).add (Melds.sum _ _ fun i _ => by
      simpa using Melds.consecutive (a + i * k) (Melds.empty : Melds k 0))
  · have hshift := sequence_chain_shift k a n
    rw [hsplit]
    calc
      _ = sequenceHand k (starts \ path) +
          ({a} + ∑ i ∈ Finset.range n,
            Multiset.Ico (a + i * k + 1) (a + i * k + 1 + k)) := by ac_rfl
      _ = sequenceHand k (starts \ path) + (shifted + {a + n * k}) := by
        rw [← hshift]
      _ = _ := by ac_rfl

/-- Equal multiples of the meld size at selected possible eye ranks. -/
def eyeBlocks (k q : ℕ) (eyes : Finset ℕ) : Multiset ℕ :=
  ∑ e ∈ eyes, Multiset.replicate (k * q) e

/-- Endpoint transfers turn eye blocks and a sequence family into a full wait. -/
theorem fullWait_of_transfers (k q ranks : ℕ) (eyes starts : Finset ℕ)
    (heyes : ∀ e ∈ eyes, e < ranks)
    (hstarts : ∀ s ∈ starts, s + k ≤ ranks)
    (htransfer : ∀ draw < ranks, ∃ e ∈ eyes, ∃ rest, Melds k rest ∧
      sequenceHand k starts + {draw} = {e} + rest) :
    FullWait k (1 + k * q) ranks (eyeBlocks k q eyes + sequenceHand k starts) := by
  classical
  constructor
  · intro tile htile
    rcases Multiset.mem_add.mp htile with heye | hseq
    · obtain ⟨e, he, htile⟩ := Multiset.mem_sum.mp heye
      rw [Multiset.eq_of_mem_replicate htile]
      exact heyes e he
    · obtain ⟨s, hs, htile⟩ := Multiset.mem_sum.mp hseq
      have ht := Multiset.mem_Ico.mp htile
      exact ht.2.trans_le (hstarts s hs)
  · intro draw hdraw
    obtain ⟨e, he, rest, hm, hmove⟩ := htransfer draw hdraw
    let others := eyeBlocks k q (eyes.erase e)
    refine ⟨e, others + rest, ?_, ?_⟩
    · exact (Melds.sum _ _ fun t _ => Melds.replicate_mul q t).add hm
    · have hsplit : others + Multiset.replicate (k * q) e = eyeBlocks k q eyes :=
        Finset.sum_erase_add _ _ he
      rw [add_assoc, hmove, ← hsplit]
      simp only [Multiset.replicate_add, Multiset.replicate_one]
      ac_rfl

/-- The total number of tiles in the construction is explicit. -/
theorem card_eyeBlocks_add_sequenceHand (k q : ℕ) (eyes starts : Finset ℕ) :
    (eyeBlocks k q eyes + sequenceHand k starts).card =
      k * q * eyes.card + k * starts.card := by
  have hcard (s : ℕ) : (Multiset.Ico s (s + k)).card = k := by
    change (Finset.Ico s (s + k)).card = k
    simp
  simp [eyeBlocks, sequenceHand, Multiset.card_sum, hcard, Nat.mul_comm]

end MeldSizeObstruction
