module

public import MeldSizeObstruction.PeriodicConstruction

/-!
# Lower bounds for the number of winning melds

With at least four residue classes, every winning eye has the draw's residue.
This forces at least `p-1` waiting tiles in each residue class.
-/

set_option autoImplicit false

@[expose] public section

namespace MeldSizeObstruction

variable {k p ranks : ℕ}

/-- The unreduced number of tiles in a rank-residue class. -/
def residueSize (k : ℕ) (h : Multiset ℕ) (r : Fin k) : ℕ :=
  (h.map (· % k)).count r.val

/-- The residue-class sizes partition the hand. -/
theorem sum_residueSize (hk : 0 < k) (h : Multiset ℕ) :
    (∑ r : Fin k, residueSize k h r) = h.card := by
  simp only [residueSize]
  rw [Fin.sum_univ_eq_sum_range (fun r => (h.map (· % k)).count r) k]
  rw [Multiset.sum_count_eq_card]
  · simp
  · intro a ha
    obtain ⟨tile, _, rfl⟩ := Multiset.mem_map.mp ha
    exact Finset.mem_range.mpr (Nat.mod_lt _ hk)

/-- A rank's multiplicity is at most its residue class's size. -/
theorem count_le_residueSize (h : Multiset ℕ) (r : Fin k) (tile : ℕ)
    (hr : tile % k = r.val) : h.count tile ≤ residueSize k h r := by
  rw [residueSize, Multiset.count_map]
  simpa [Multiset.count_filter, hr] using
    Multiset.count_le_card tile (h.filter (fun t => r.val = t % k))

/-- Every winning decomposition of a full wait uses an eye in the draw's class. -/
theorem FullWait.eye_residue {h rest : Multiset ℕ} (hw : FullWait k p ranks h)
    (hk : 4 ≤ k) (hkr : k ≤ ranks) (draw eye : ℕ)
    (hm : Melds k rest) (hdecomp : h + {draw} = Multiset.replicate p eye + rest) :
    eye % k = draw % k := by
  classical
  have hkpos : 0 < k := by omega
  have : Fact (1 < k) := ⟨by omega⟩
  obtain ⟨hp, hC⟩ := hw.obstruction hk hkr
  obtain ⟨a, ha⟩ := hm.residueCounts_constant
  let d := rankResidue hkpos draw
  let e := rankResidue hkpos eye
  have hc (r : Fin k) : residueCounts k h r + pointMass d r = pointMass e r + a := by
    have hsingle : residueCounts k ({draw} : Multiset ℕ) r = pointMass d r := by
      simpa using residueCounts_replicate hkpos 1 draw r
    have heq := congrArg (fun hand => residueCounts k hand r) hdecomp
    simpa only [residueCounts_add, hsingle, residueCounts_replicate hkpos, hp, one_mul, ha r]
      using heq
  by_contra hne
  have hde : d ≠ e := by
    intro heq
    have hv := congrArg Fin.val heq
    exact hne hv.symm
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({d, e} : Finset (Fin k)).card < (Finset.univ : Finset (Fin k)).card by
      have := (Finset.card_le_two : ({d, e} : Finset (Fin k)).card ≤ 2)
      simpa using (show ({d, e} : Finset (Fin k)).card < k by omega))
  have hr' : r ≠ d ∧ r ≠ e := by simpa using hr
  have hout : residueCounts k h r = a := by
    simpa [pointMass, hr'.1, hr'.2] using hc r
  have hdraw : residueCounts k h d + 1 = a := by
    simpa [pointMass, hde] using hc d
  rw [hC d r, hout] at hdraw
  have hbad : (1 : ZMod k) = 0 := by linear_combination hdraw
  exact one_ne_zero hbad

/-- At least `p-1` waiting tiles are needed in every residue class. -/
theorem FullWait.residueSize_lower {h : Multiset ℕ} (hw : FullWait k p ranks h)
    (hk : 4 ≤ k) (hkr : k ≤ ranks) (r : Fin k) : p - 1 ≤ residueSize k h r := by
  obtain ⟨eye, rest, hm, hdecomp⟩ := hw.2 r.val (r.isLt.trans_le hkr)
  have heye := hw.eye_residue hk hkr r.val eye hm hdecomp
  have hrmod : r.val % k = r.val := Nat.mod_eq_of_lt r.isLt
  have hc := congrArg (fun hand : Multiset ℕ => (hand.map (· % k)).count r.val) hdecomp
  simp only [Multiset.map_add, Multiset.count_add, Multiset.map_singleton,
    Multiset.count_singleton, Multiset.map_replicate, Multiset.count_replicate,
    heye, hrmod] at hc
  change residueSize k h r + 1 = p + residueSize k rest r at hc
  omega

/-- Summing the class capacities gives a lower bound on the hand size. -/
theorem FullWait.card_lower {h : Multiset ℕ} (hw : FullWait k p ranks h)
    (hk : 4 ≤ k) (hkr : k ≤ ranks) : k * (p - 1) ≤ h.card := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun r _ => hw.residueSize_lower hk hkr r)
  simpa [sum_residueSize (by omega : 0 < k)] using hsum

/-- An eye of size `1+k*q` requires at least `q*(k-1)` winning melds. -/
theorem FullWait.meld_count_lower {h : Multiset ℕ} {q m : ℕ}
    (hw : FullWait k (1 + k * q) ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks)
    (hcard : h.card + 1 = (1 + k * q) + k * m) : q * (k - 1) ≤ m := by
  have hlower := hw.card_lower hk hkr
  have hpred : k - 1 + 1 = k := by omega
  have hprod := congrArg (fun x => k * q * x) hpred
  simp only [Nat.add_sub_cancel_left] at hlower
  nlinarith

private theorem eye_eq_draw_of_tight {h rest : Multiset ℕ}
    (hw : FullWait k p ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks) (hp : 0 < p)
    (r : Fin k) (draw eye : ℕ) (hdraw : draw % k = r.val)
    (htight : residueSize k h r = p - 1)
    (hm : Melds k rest) (hdecomp : h + {draw} = Multiset.replicate p eye + rest) :
    eye = draw := by
  by_contra hne
  have heye := (hw.eye_residue hk hkr draw eye hm hdecomp).trans hdraw
  have hcapacity := count_le_residueSize h r eye heye
  have hc := congrArg (fun hand : Multiset ℕ => hand.count eye) hdecomp
  simp [hne] at hc
  omega

private theorem count_draw_of_tight {h : Multiset ℕ} (hw : FullWait k p ranks h)
    (hk : 4 ≤ k) (hkr : k ≤ ranks) (hp : 0 < p) (r : Fin k) (draw : ℕ)
    (hdraw : draw < ranks) (hres : draw % k = r.val)
    (htight : residueSize k h r = p - 1) : p - 1 ≤ h.count draw := by
  obtain ⟨eye, rest, hm, hdecomp⟩ := hw.2 draw hdraw
  have heq := eye_eq_draw_of_tight hw hk hkr hp r draw eye hres htight hm hdecomp
  subst eye
  have hc := congrArg (fun hand : Multiset ℕ => hand.count draw) hdecomp
  simp at hc
  omega

/-- More than `k` drawable ranks require strictly more than the capacity bound. -/
theorem FullWait.card_strict_lower {h : Multiset ℕ} (hw : FullWait k p ranks h)
    (hk : 4 ≤ k) (hkr : k < ranks) (hp : 1 < p) : k * (p - 1) < h.card := by
  classical
  have hkpos : 0 < k := by omega
  have hlower := hw.card_lower hk hkr.le
  by_contra hn
  have hcard : h.card = k * (p - 1) := by omega
  have hsum : (∑ _r : Fin k, (p - 1)) = ∑ r : Fin k, residueSize k h r := by
    simp [sum_residueSize hkpos h, hcard]
  have htight : ∀ r : Fin k, residueSize k h r = p - 1 := by
    have hall := (Finset.sum_eq_sum_iff_of_le
      (fun r (_ : r ∈ (Finset.univ : Finset (Fin k))) =>
        hw.residueSize_lower hk hkr.le r)).mp hsum
    exact fun r => (hall r (Finset.mem_univ r)).symm
  let r := rankResidue hkpos 0
  have hzero : p - 1 ≤ h.count 0 := count_draw_of_tight hw hk hkr.le (by omega)
    r 0 (by omega) (by simp [r, rankResidue]) (htight r)
  have hlast : p - 1 ≤ h.count k := count_draw_of_tight hw hk hkr.le (by omega)
    r k hkr (by simp [r, rankResidue]) (htight r)
  let fiber := h.filter (fun t => 0 = t % k)
  have hsize : fiber.card = p - 1 := by
    simpa [residueSize, Multiset.count_map, r, rankResidue, fiber] using htight r
  have hcount : fiber.count 0 = fiber.card := by
    have hle := Multiset.count_le_card 0 fiber
    have heq : fiber.count 0 = h.count 0 := by simp [fiber, Multiset.count_filter]
    omega
  have hk_mem : k ∈ fiber := by
    apply Multiset.mem_filter.mpr
    exact ⟨Multiset.count_pos.mp (by omega), by simp⟩
  have heq := (Multiset.count_eq_card.mp hcount) k hk_mem
  omega

/-- Positive `q` needs an extra meld as soon as the suit extends past `k` ranks. -/
theorem FullWait.meld_count_strict_lower {h : Multiset ℕ} {q m : ℕ}
    (hw : FullWait k (1 + k * q) ranks h) (hk : 4 ≤ k) (hkr : k < ranks)
    (hq : 0 < q) (hcard : h.card + 1 = (1 + k * q) + k * m) :
    q * (k - 1) + 1 ≤ m := by
  have hlower := hw.card_strict_lower hk hkr (by nlinarith : 1 < 1 + k * q)
  have hpred : k - 1 + 1 = k := by omega
  have hprod := congrArg (fun x => k * q * x) hpred
  simp only [Nat.add_sub_cancel_left] at hlower
  nlinarith

/-- With exactly `k` ranks, the lower bound on meld count is attained. -/
theorem exists_fullWait_at_capacity (q : ℕ) (hk : 2 ≤ k) :
    ∃ h : Multiset ℕ, FullWait k (1 + k * q) k h ∧
      h.card + 1 = (1 + k * q) + k * (q * (k - 1)) := by
  simpa [periodicMeldCount] using exists_fullWait_periodic (k := k) (ranks := k)
    q hk le_rfl

/-- One or two extra ranks admit a construction one meld above the capacity bound. -/
theorem exists_fullWait_short_extension (q extra : ℕ) (hk : 4 ≤ k)
    (hextra : 1 ≤ extra) (hextra' : extra ≤ 2) :
    ∃ h : Multiset ℕ, FullWait k (1 + k * q) (k + extra) h ∧
      h.card + 1 = (1 + k * q) + k * (q * (k - 1) + 1) := by
  have hcount : periodicMeldCount k q (k + extra) = q * (k - 1) + 1 := by
    have hsmall : extra < k := by omega
    simp only [periodicMeldCount, Nat.add_sub_cancel_left, Nat.div_eq_of_lt hsmall,
      Nat.mod_eq_of_lt hsmall, zero_mul, Nat.add_zero]
    omega
  simpa only [hcount] using exists_fullWait_periodic (k := k) (ranks := k + extra)
    q (by omega) (by omega)

/-- Exact minimum meld counts for suits with `k`, `k+1`, or `k+2` ranks.
The single-tile-eye exception is excluded by `0 < q`. -/
theorem minimum_meld_count_short {q : ℕ} (hk : 4 ≤ k) (hq : 0 < q)
    (hkr : k ≤ ranks) (hranks : ranks ≤ k + 2) :
    let minimum := q * (k - 1) + if ranks = k then 0 else 1
    (∃ h : Multiset ℕ, FullWait k (1 + k * q) ranks h ∧
      h.card + 1 = (1 + k * q) + k * minimum) ∧
    ∀ (h : Multiset ℕ) (m : ℕ), FullWait k (1 + k * q) ranks h →
      h.card + 1 = (1 + k * q) + k * m → minimum ≤ m := by
  dsimp only
  by_cases heq : ranks = k
  · subst ranks
    constructor
    · simpa using exists_fullWait_at_capacity q (by omega : 2 ≤ k)
    · intro h m hw hc
      simpa using hw.meld_count_lower hk le_rfl hc
  · have hstrict : k < ranks := by omega
    have hextra : k + (ranks - k) = ranks := by omega
    constructor
    · have hexists := exists_fullWait_short_extension q (ranks - k) hk (by omega) (by omega)
      simpa [heq, hextra] using hexists
    · intro h m hw hc
      simpa [heq] using hw.meld_count_strict_lower hk hstrict hq hc

end MeldSizeObstruction
