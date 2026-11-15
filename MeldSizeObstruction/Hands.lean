module

public import MeldSizeObstruction
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Tile hands and the residue obstruction

Hands are finite multisets of natural-number ranks. A meld consists of `k`
identical tiles or of one tile at each rank in `[start, start + k)`.
A winning hand consists of such melds and one eye of `p` identical tiles.

`FullWait k p ranks h` restricts the hand and its possible draws to ranks
below `ranks`. Exact multiset equality in a winning decomposition prevents
the decomposition from introducing any tile outside the winning hand.

The uniform construction gives full waits for every eye size `1 + k*q`.
Together with the obstruction, this classifies existence when `k ≥ 4` and
the suit has at least `k` ranks, allowing the meld count to vary.
-/

set_option autoImplicit false

@[expose] public section

namespace MeldSizeObstruction

variable {k p ranks : ℕ}

/-- The residue class of a natural-number rank. -/
def rankResidue (hk : 0 < k) (tile : ℕ) : Fin k :=
  ⟨tile % k, Nat.mod_lt tile hk⟩

/-- Tile counts in each rank-residue class, reduced modulo the meld size. -/
def residueCounts (k : ℕ) (hand : Multiset ℕ) (r : Fin k) : ZMod k :=
  ((hand.map (· % k)).count r.val : ℕ)

@[simp]
theorem residueCounts_zero (r : Fin k) : residueCounts k 0 r = 0 := by
  simp [residueCounts]

@[simp]
theorem residueCounts_add (h g : Multiset ℕ) (r : Fin k) :
    residueCounts k (h + g) r = residueCounts k h r + residueCounts k g r := by
  simp [residueCounts]

/-- Repeated identical tiles contribute only to the tile's residue class. -/
theorem residueCounts_replicate (hk : 0 < k) (n tile : ℕ) (r : Fin k) :
    residueCounts k (Multiset.replicate n tile) r =
      (n : ZMod k) * pointMass (rankResidue hk tile) r := by
  simp [residueCounts, Multiset.count_replicate, pointMass, rankResidue,
    Fin.ext_iff, eq_comm]

/-- A whole identical meld has zero residue counts modulo `k`. -/
@[simp]
theorem residueCounts_identical (tile : ℕ) (r : Fin k) :
    residueCounts k (Multiset.replicate k tile) r = 0 := by
  simp only [residueCounts, Multiset.map_replicate, Multiset.count_replicate]
  split_ifs <;> simp

/-- A consecutive meld contributes one tile in every rank-residue class. -/
@[simp]
theorem residueCounts_consecutive (start : ℕ) (r : Fin k) :
    residueCounts k (Multiset.Ico start (start + k)) r = 1 := by
  rw [residueCounts, Nat.multiset_Ico_map_mod]
  rw [Multiset.count_eq_one_of_mem (Multiset.nodup_range k)
    (Multiset.mem_range.mpr r.isLt)]
  simp

/-- A finite union of identical and consecutive `k`-tile melds. -/
inductive Melds (k : ℕ) : Multiset ℕ → Prop
  | empty : Melds k 0
  | identical (tile : ℕ) {rest : Multiset ℕ} :
      Melds k rest → Melds k (Multiset.replicate k tile + rest)
  | consecutive (start : ℕ) {rest : Multiset ℕ} :
      Melds k rest → Melds k (Multiset.Ico start (start + k) + rest)

/-- A union of melds has equal residue counts modulo `k`. -/
theorem Melds.residueCounts_constant {h : Multiset ℕ} (hm : Melds k h) :
    ∃ a : ZMod k, ∀ r : Fin k, residueCounts k h r = a := by
  induction hm with
  | empty => exact ⟨0, residueCounts_zero⟩
  | identical tile _ ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨a, fun r => by simp [ha r]⟩
  | consecutive start _ ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨1 + a, fun r => by simp [ha r]⟩

/-- A meld decomposition has a whole number of `k`-tile blocks. -/
theorem Melds.card {h : Multiset ℕ} (hm : Melds k h) :
    ∃ n : ℕ, h.card = k * n := by
  induction hm with
  | empty => exact ⟨0, by simp⟩
  | identical tile _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [hn, Nat.mul_add, Nat.add_comm]⟩
  | consecutive start _ ih =>
    obtain ⟨n, hn⟩ := ih
    have hc : (Multiset.Ico start (start + k)).card = k := by
      change (Finset.Ico start (start + k)).card = k
      simp
    refine ⟨n + 1, ?_⟩
    rw [Multiset.card_add, hc, hn, Nat.mul_succ]
    exact Nat.add_comm _ _

/-- Combining two decompositions gives another meld decomposition. -/
theorem Melds.add {h g : Multiset ℕ} (hh : Melds k h) (hg : Melds k g) :
    Melds k (h + g) := by
  induction hh with
  | empty => simpa using hg
  | identical tile _ ih =>
    simpa only [add_assoc] using Melds.identical tile ih
  | consecutive start _ ih =>
    simpa only [add_assoc] using Melds.consecutive start ih

/-- A multiple of `k` identical tiles splits into identical melds. -/
theorem Melds.replicate_mul (q tile : ℕ) : Melds k (Multiset.replicate (k * q) tile) := by
  induction q with
  | zero => simpa using (Melds.empty : Melds k 0)
  | succ q ih =>
    rw [Nat.mul_succ, Multiset.replicate_add]
    exact ih.add (by simpa using Melds.identical tile (Melds.empty : Melds k 0))

/-- Each rank's decomposition can be combined over any finite set of ranks. -/
theorem Melds.sum (s : Finset ℕ) (f : ℕ → Multiset ℕ)
    (hf : ∀ tile ∈ s, Melds k (f tile)) : Melds k (∑ tile ∈ s, f tile) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Melds.empty : Melds k 0)
  | @insert tile s hnot ih =>
    rw [Finset.sum_insert hnot]
    exact (hf tile (by simp)).add (ih fun t ht => hf t (by simp [ht]))

/-- A hand decomposes exactly into melds and an eye of `p` identical tiles. -/
def WinningHand (k p : ℕ) (hand : Multiset ℕ) : Prop :=
  ∃ eye rest, Melds k rest ∧ hand = Multiset.replicate p eye + rest

/-- A winning hand has `p` eye tiles and a whole number of `k`-tile blocks. -/
theorem WinningHand.card {h : Multiset ℕ} (hw : WinningHand k p h) :
    ∃ n : ℕ, h.card = p + k * n := by
  obtain ⟨eye, rest, hm, rfl⟩ := hw
  obtain ⟨n, hn⟩ := hm.card
  exact ⟨n, by simp [hn]⟩

/-- A bounded hand wins after drawing any rank in the suit. -/
def FullWait (k p ranks : ℕ) (hand : Multiset ℕ) : Prop :=
  (∀ tile ∈ hand, tile < ranks) ∧
    ∀ tile < ranks, WinningHand k p (hand + {tile})

/-- Drawing every rank covers every residue when the suit has at least `k` ranks. -/
theorem FullWait.residueCompatible {h : Multiset ℕ} (hw : FullWait k p ranks h)
    (hk : 0 < k) (hranks : k ≤ ranks) :
    ResidueCompatible (residueCounts k h) (p : ZMod k) := by
  intro i
  obtain ⟨eye, rest, hm, hdecomp⟩ := hw.2 i.val (i.isLt.trans_le hranks)
  obtain ⟨a, ha⟩ := hm.residueCounts_constant
  refine ⟨rankResidue hk eye, a, ?_⟩
  intro r
  have hdraw : rankResidue hk i.val = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  have hsingle : residueCounts k ({i.val} : Multiset ℕ) r = pointMass i r := by
    simpa [hdraw] using residueCounts_replicate hk 1 i.val r
  have hc := congrArg (fun hand => residueCounts k hand r) hdecomp
  simp only [residueCounts_add, hsingle, residueCounts_replicate hk, ha r] at hc
  apply sub_eq_iff_eq_add.mpr
  simpa only [add_comm] using hc

/-- Actual full-sided waits obey the eye-size and equal-class-count obstruction. -/
theorem FullWait.obstruction {h : Multiset ℕ} (hw : FullWait k p ranks h)
    (hk : 4 ≤ k) (hranks : k ≤ ranks) :
    (p : ZMod k) = 1 ∧ ∀ r s : Fin k, residueCounts k h r = residueCounts k h s :=
  (residue_compatible_iff hk _ _).mp (hw.residueCompatible (by omega) hranks)

/-- The eye size of an actual full-sided wait is one modulo the meld size. -/
theorem FullWait.eye_mod_one {h : Multiset ℕ} (hw : FullWait k p ranks h)
    (hk : 4 ≤ k) (hranks : k ≤ ranks) : p % k = 1 := by
  have hp := (ZMod.natCast_eq_natCast_iff' p 1 k).mp (by
    simpa using (hw.obstruction hk hranks).1)
  simpa [Nat.mod_eq_of_lt (show 1 < k by omega)] using hp

/-- An ordinary pair cannot be the eye of a full-sided wait with larger melds. -/
theorem not_fullWait_pair (hk : 4 ≤ k) (hranks : k ≤ ranks) (h : Multiset ℕ) :
    ¬ FullWait k 2 ranks h := by
  intro hw
  have hp := hw.eye_mod_one hk hranks
  rw [Nat.mod_eq_of_lt (show 2 < k by omega)] at hp
  omega

/-- An eye one tile smaller than the meld also cannot give a full-sided wait. -/
theorem not_fullWait_pred (hk : 4 ≤ k) (hranks : k ≤ ranks) (h : Multiset ℕ) :
    ¬ FullWait k (k - 1) ranks h := by
  intro hw
  have hp := hw.eye_mod_one hk hranks
  rw [Nat.mod_eq_of_lt (show k - 1 < k by omega)] at hp
  omega

/-- A hand with `k*q` tiles of every rank and an extra identical meld at zero. -/
def uniformHand (k q ranks : ℕ) : Multiset ℕ :=
  (∑ tile ∈ Finset.range ranks, Multiset.replicate (k * q) tile) +
    Multiset.replicate k 0

/-- Every eye size of the form `1 + k*q` has an explicit full-sided wait. -/
theorem fullWait_uniform (k q : ℕ) (hranks : 0 < ranks) :
    FullWait k (1 + k * q) ranks (uniformHand k q ranks) := by
  classical
  constructor
  · intro tile htile
    rcases Multiset.mem_add.mp htile with hblock | hzero
    · obtain ⟨t, ht, htile⟩ := Multiset.mem_sum.mp hblock
      rw [Multiset.eq_of_mem_replicate htile]
      exact Finset.mem_range.mp ht
    · simpa [Multiset.eq_of_mem_replicate hzero] using hranks
  · intro tile ht
    let s := (Finset.range ranks).erase tile
    let rest := (∑ t ∈ s, Multiset.replicate (k * q) t) + Multiset.replicate k 0
    refine ⟨tile, rest, ?_, ?_⟩
    · exact (Melds.sum s _ (fun t _ => Melds.replicate_mul q t)).add
        (by simpa using Melds.identical 0 (Melds.empty : Melds k 0))
    · have hsplit : (∑ t ∈ s, Multiset.replicate (k * q) t) +
          Multiset.replicate (k * q) tile =
          ∑ t ∈ Finset.range ranks, Multiset.replicate (k * q) t :=
        Finset.sum_erase_add _ _ (Finset.mem_range.mpr ht)
      simp only [uniformHand, rest, Multiset.replicate_add, Multiset.replicate_one]
      rw [← hsplit]
      ac_rfl

/-- Full-sided waits exist exactly for eye sizes congruent to one modulo `k`.
Tile multiplicities and the choice of meld count are unrestricted. -/
theorem exists_fullWait_iff (hk : 4 ≤ k) (hranks : k ≤ ranks) :
    (∃ h : Multiset ℕ, FullWait k p ranks h) ↔ p % k = 1 := by
  constructor
  · rintro ⟨h, hw⟩
    exact hw.eye_mod_one hk hranks
  · intro hp
    refine ⟨uniformHand k (p / k) ranks, ?_⟩
    have hpform : 1 + k * (p / k) = p := by
      simpa only [hp] using Nat.mod_add_div p k
    simpa only [hpform] using fullWait_uniform k (p / k) (by omega : 0 < ranks)

end MeldSizeObstruction
