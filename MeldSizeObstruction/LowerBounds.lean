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

theorem residueSize_add (h g : Multiset ℕ) (r : Fin k) :
    residueSize k (h + g) r = residueSize k h r + residueSize k g r := by
  simp [residueSize]

theorem residueSize_consecutive (start : ℕ) (r : Fin k) :
    residueSize k (Multiset.Ico start (start + k)) r = 1 := by
  rw [residueSize, Nat.multiset_Ico_map_mod]
  exact Multiset.count_eq_one_of_mem (Multiset.nodup_range k) (Multiset.mem_range.mpr r.isLt)

/-- A residue with one tile in a meld decomposition forces a consecutive meld. -/
theorem Melds.exists_consecutive_of_residueSize_eq_one {h : Multiset ℕ}
    (hm : Melds k h) (hk : 1 < k) (r : Fin k) (hsize : residueSize k h r = 1) :
    ∃ start, Multiset.Ico start (start + k) ≤ h := by
  induction hm with
  | empty => simp [residueSize] at hsize
  | identical tile _ ih =>
    rw [residueSize_add] at hsize
    simp only [residueSize, Multiset.map_replicate, Multiset.count_replicate] at hsize
    split_ifs at hsize with hres
    · omega
    · obtain ⟨start, hstart⟩ := ih (by simpa [residueSize] using hsize)
      exact ⟨start, hstart.trans (by simp)⟩
  | consecutive start _ _ =>
    exact ⟨start, by simp⟩

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

private theorem count_add_count_le_residueSize (h : Multiset ℕ) (r : Fin k)
    {a b : ℕ} (ha : a % k = r.val) (hb : b % k = r.val) (hab : a ≠ b) :
    h.count a + h.count b ≤ residueSize k h r := by
  let fiber := h.filter (fun tile => r.val = tile % k)
  have hcard : fiber.card = residueSize k h r := by
    simp [fiber, residueSize, Multiset.count_map]
  have hca : fiber.count a = h.count a := by
    simp [fiber, ha]
  have hcb : fiber.count b = h.count b := by
    simp [fiber, hb]
  have hsubset :
      Multiset.replicate (fiber.count a) a + Multiset.replicate (fiber.count b) b ≤ fiber := by
    rw [Multiset.le_iff_count]
    intro tile
    by_cases hta : tile = a
    · subst tile
      simp [Multiset.count_replicate, Ne.symm hab]
    by_cases htb : tile = b
    · subst tile
      simp [Multiset.count_replicate, hab]
    simp [Multiset.count_replicate, Ne.symm hta, Ne.symm htb]
  simpa [hcard, hca, hcb] using Multiset.card_le_card hsubset

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

private theorem count_draw_of_no_other_eye {h : Multiset ℕ} (hw : FullWait k p ranks h)
    (hk : 4 ≤ k) (hkr : k ≤ ranks) (r : Fin k) (draw : ℕ)
    (hdraw : draw < ranks) (hres : draw % k = r.val)
    (hother : ∀ eye, eye % k = r.val → eye ≠ draw → h.count eye < p) :
    p - 1 ≤ h.count draw := by
  obtain ⟨eye, rest, hm, hdecomp⟩ := hw.2 draw hdraw
  have heq : eye = draw := by
    by_contra hne
    have heye := (hw.eye_residue hk hkr draw eye hm hdecomp).trans hres
    have hsmall := hother eye heye hne
    have hc := congrArg (fun hand : Multiset ℕ => hand.count eye) hdecomp
    simp [hne] at hc
    omega
  subst eye
  have hc := congrArg (fun hand : Multiset ℕ => hand.count draw) hdecomp
  simp at hc
  omega

/-- Two possible draws in a residue class force at least a whole eye in that class. -/
theorem FullWait.residueSize_ge_eye_of_distinct_draws {h : Multiset ℕ}
    (hw : FullWait k p ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks) (hp : 1 < p)
    (r : Fin k) {x y : ℕ} (hx : x < ranks) (hy : y < ranks)
    (hxres : x % k = r.val) (hyres : y % k = r.val) (hxy : x ≠ y) :
    p ≤ residueSize k h r := by
  by_contra! hlt
  have hsmall (eye : ℕ) (heye : eye % k = r.val) : h.count eye < p :=
    lt_of_le_of_lt (count_le_residueSize h r eye heye) hlt
  have hcx := count_draw_of_no_other_eye hw hk hkr r x hx hxres
    (fun eye heye _ => hsmall eye heye)
  have hcy := count_draw_of_no_other_eye hw hk hkr r y hy hyres
    (fun eye heye _ => hsmall eye heye)
  have hpair := count_add_count_le_residueSize h r hxres hyres hxy
  omega

/-- A repeated residue with exactly enough tiles for an eye holds them at one rank. -/
theorem FullWait.exists_full_eye_of_distinct_draws {h : Multiset ℕ}
    (hw : FullWait k p ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks) (hp : 2 < p)
    (r : Fin k) {x y : ℕ} (hx : x < ranks) (hy : y < ranks)
    (hxres : x % k = r.val) (hyres : y % k = r.val) (hxy : x ≠ y)
    (hsize : residueSize k h r = p) :
    ∃ eye, eye % k = r.val ∧ h.count eye = p := by
  by_contra! hnone
  have hsmall (eye : ℕ) (heye : eye % k = r.val) : h.count eye < p := by
    have hle := count_le_residueSize h r eye heye
    have hne := hnone eye heye
    omega
  have hcx := count_draw_of_no_other_eye hw hk hkr r x hx hxres
    (fun eye heye _ => hsmall eye heye)
  have hcy := count_draw_of_no_other_eye hw hk hkr r y hy hyres
    (fun eye heye _ => hsmall eye heye)
  have hpair := count_add_count_le_residueSize h r hxres hyres hxy
  omega

/-- At total size `k*p`, two classes that can supply whole eyes force all class sizes to be `p`. -/
theorem FullWait.residueSize_eq_eye_of_card {h : Multiset ℕ}
    (hw : FullWait k p ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks) (hp : 0 < p)
    (hcard : h.card = k * p) {a b : Fin k} (hab : a ≠ b)
    (ha : p ≤ residueSize k h a) (hb : p ≤ residueSize k h b)
    (r : Fin k) : residueSize k h r = p := by
  classical
  let excess (s : Fin k) := residueSize k h s - (p - 1)
  have hadd (s : Fin k) : excess s + (p - 1) = residueSize k h s :=
    Nat.sub_add_cancel (hw.residueSize_lower hk hkr s)
  have htotal :
      (∑ s : Fin k, excess s) + k * (p - 1) = k * p := by
    calc
      _ = ∑ s : Fin k, (excess s + (p - 1)) := by simp [Finset.sum_add_distrib]
      _ = k * p := by simp [hadd, sum_residueSize (by omega : 0 < k), hcard]
  have hmul : k * (p - 1) + k = k * p := by
    calc
      _ = k * (p - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = k * p := by rw [Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hsum : (∑ s : Fin k, excess s) = k := by omega
  have hpa := hadd a
  have hpb := hadd b
  have hpair : excess a + excess b ≤ ∑ s : Fin k, excess s := by
    rw [← Finset.sum_pair (f := excess) hab]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hlt : excess a < k := by omega
  have hpos (s : Fin k) : 1 ≤ excess s := by
    have hcongr : (residueSize k h s : ZMod k) = (residueSize k h a : ZMod k) :=
      (hw.obstruction hk hkr).2 s a
    have hcast : (excess s : ZMod k) = (excess a : ZMod k) := by
      apply add_right_cancel (b := ((p - 1 : ℕ) : ZMod k))
      simpa only [← Nat.cast_add, hadd] using hcongr
    have hmod : excess s % k = excess a := by
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] using congrArg ZMod.val hcast
    have hle := Nat.mod_le (excess s) k
    omega
  have hall := (Finset.sum_eq_sum_iff_of_le
    (fun s (_ : s ∈ (Finset.univ : Finset (Fin k))) => hpos s)).mp (by simp [hsum])
  have hone := hall r (Finset.mem_univ r)
  have hr := hadd r
  omega

private theorem eq_of_mem_of_full_eye {h : Multiset ℕ} (r : Fin k) {tile anchor : ℕ}
    (htile : tile ∈ h) (hres : tile % k = r.val) (hanchor : anchor % k = r.val)
    (hcount : h.count anchor = p) (hsize : residueSize k h r = p) : tile = anchor := by
  by_contra hne
  have hpair := count_add_count_le_residueSize h r hres hanchor hne
  have hpos := Multiset.count_pos.mpr htile
  omega

private theorem consecutive_contains_residue (start : ℕ) (r : Fin k) :
    ∃ tile ∈ Multiset.Ico start (start + k), tile % k = r.val := by
  apply Multiset.mem_map.mp
  apply Multiset.count_pos.mp
  change 0 < residueSize k (Multiset.Ico start (start + k)) r
  rw [residueSize_consecutive]
  decide

private theorem FullWait.exists_consecutive_with_draw {h : Multiset ℕ}
    (hw : FullWait k p ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks) (hp : 1 < p)
    (r : Fin k) {draw anchor : ℕ} (hdraw : draw < ranks) (hres : draw % k = r.val)
    (hanchor : anchor % k = r.val) (hcount : h.count anchor = p)
    (hsize : residueSize k h r = p) :
    ∃ start, draw ∈ Multiset.Ico start (start + k) ∧
      Multiset.Ico start (start + k) ≤ h + {draw} := by
  obtain ⟨eye, rest, hm, hdecomp⟩ := hw.2 draw hdraw
  have heyeMem : eye ∈ h := by
    apply Multiset.count_pos.mp
    have hc := congrArg (fun hand : Multiset ℕ => hand.count eye) hdecomp
    simp only [Multiset.count_add, Multiset.count_singleton, Multiset.count_replicate,
      eq_self, ite_true] at hc
    split_ifs at hc <;> omega
  have heyeRes := (hw.eye_residue hk hkr draw eye hm hdecomp).trans hres
  have heye := eq_of_mem_of_full_eye r heyeMem heyeRes hanchor hcount hsize
  subst eye
  have hsingle : residueSize k ({draw} : Multiset ℕ) r = 1 := by
    simp [residueSize, hres]
  have hreplicate : residueSize k (Multiset.replicate p anchor) r = p := by
    simp only [residueSize, Multiset.map_replicate, Multiset.count_replicate, hanchor, eq_self, ite_true]
  have hrest : residueSize k rest r = 1 := by
    have heq := congrArg (fun hand => residueSize k hand r) hdecomp
    rw [residueSize_add, residueSize_add, hsize, hsingle, hreplicate] at heq
    omega
  have hdrawMem : draw ∈ rest := by
    apply Multiset.count_pos.mp
    have hc := congrArg (fun hand : Multiset ℕ => hand.count draw) hdecomp
    simp only [Multiset.count_add, Multiset.count_singleton, Multiset.count_replicate,
      eq_self, ite_true] at hc
    split_ifs at hc with he
    · subst draw
      omega
    · omega
  obtain ⟨start, hs⟩ := hm.exists_consecutive_of_residueSize_eq_one (by omega) r hrest
  obtain ⟨tile, htile, htileRes⟩ := consecutive_contains_residue start r
  have heq : tile = draw := by
    by_contra hne
    have hpair := count_add_count_le_residueSize rest r htileRes hres hne
    have htpos := Multiset.count_pos.mpr (Multiset.mem_of_le hs htile)
    have hdpos := Multiset.count_pos.mpr hdrawMem
    omega
  refine ⟨start, heq ▸ htile, ?_⟩
  rw [hdecomp]
  exact hs.trans (by simp)

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
  have hlarge := hw.residueSize_ge_eye_of_distinct_draws hk hkr.le hp r
    (x := 0) (y := k) (by omega) hkr
    (by simp [r, rankResidue]) (by simp [r, rankResidue]) (by omega)
  have hsize := htight r
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

/-- With three extra ranks available, a full wait cannot hold exactly `k*p` tiles. -/
theorem FullWait.card_ne_mul_eye_of_three_extra_ranks {h : Multiset ℕ}
    (hw : FullWait k p ranks h) (hk : 4 ≤ k) (hkr : k + 3 ≤ ranks) (hp : 2 < p) :
    h.card ≠ k * p := by
  intro hcard
  have hbase : k ≤ ranks := by omega
  let r0 : Fin k := ⟨0, by omega⟩
  let r1 : Fin k := ⟨1, by omega⟩
  let r2 : Fin k := ⟨2, by omega⟩
  have h01 : r0 ≠ r1 := by
    intro heq
    have hval : (0 : ℕ) = 1 := congrArg Fin.val heq
    omega
  have hres (r : Fin k) : (r.val + k) % k = r.val := by
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
  have hcapacity (r : Fin k) (hr : r.val ≤ 2) : p ≤ residueSize k h r :=
    hw.residueSize_ge_eye_of_distinct_draws hk hbase (by omega) r
      (x := r.val) (y := r.val + k) (by omega) (by omega)
      (Nat.mod_eq_of_lt r.isLt) (hres r) (by omega)
  have hsize := hw.residueSize_eq_eye_of_card hk hbase (by omega) hcard h01
    (hcapacity r0 (by simp [r0])) (hcapacity r1 (by simp [r1]))
  have hanchor (r : Fin k) (hr : r.val ≤ 2) :
      ∃ eye, eye % k = r.val ∧ h.count eye = p :=
    hw.exists_full_eye_of_distinct_draws hk hbase hp r
      (x := r.val) (y := r.val + k) (by omega) (by omega)
      (Nat.mod_eq_of_lt r.isLt) (hres r) (by omega) (hsize r)
  obtain ⟨anchor0, ha0res, ha0count⟩ := hanchor r0 (by simp [r0])
  obtain ⟨anchor1, ha1res, ha1count⟩ := hanchor r1 (by simp [r1])
  obtain ⟨anchor2, ha2res, ha2count⟩ := hanchor r2 (by simp [r2])
  have h0mod : 0 % k = r0.val := by simp [r0]
  have h1mod : 1 % k = r1.val := Nat.mod_eq_of_lt (by omega : 1 < k)
  have h2mod : (k + 2) % k = r2.val := by
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega : 2 < k)
  -- The sequence for draw zero starts at zero and therefore uses rank one.
  obtain ⟨start0, h0mem, h0sub⟩ := hw.exists_consecutive_with_draw hk hbase (by omega) r0
    (draw := 0) (by omega) h0mod ha0res ha0count (hsize r0)
  have h0start := (Multiset.mem_Ico.mp h0mem).1
  have h1seq : 1 ∈ Multiset.Ico start0 (start0 + k) :=
    Multiset.mem_Ico.mpr ⟨by omega, by omega⟩
  have h1mem : 1 ∈ h := by
    simpa using Multiset.mem_add.mp (Multiset.mem_of_le h0sub h1seq)
  have ha1 : anchor1 = 1 :=
    (eq_of_mem_of_full_eye r1 h1mem h1mod ha1res ha1count (hsize r1)).symm
  -- The sequence for draw `k+2` also needs that same rank-one tile.
  obtain ⟨start2, h2mem, h2sub⟩ := hw.exists_consecutive_with_draw hk hbase (by omega) r2
    (draw := k + 2) (by omega) h2mod ha2res ha2count (hsize r2)
  obtain ⟨tile, htile, htileRes⟩ := consecutive_contains_residue start2 r1
  have htileMem : tile ∈ h := by
    rcases Multiset.mem_add.mp (Multiset.mem_of_le h2sub htile) with hm | hm
    · exact hm
    · have ht : tile = k + 2 := Multiset.mem_singleton.mp hm
      rw [ht, h2mod] at htileRes
      change (2 : ℕ) = 1 at htileRes
      omega
  have ht := eq_of_mem_of_full_eye r1 htileMem htileRes ha1res ha1count (hsize r1)
  rw [ht, ha1] at htile
  have hleft := (Multiset.mem_Ico.mp htile).1
  have hright := (Multiset.mem_Ico.mp h2mem).2
  omega

/-- Three or more extra ranks require at least two melds above the capacity bound. -/
theorem FullWait.meld_count_lower_of_three_extra_ranks {h : Multiset ℕ} {q m : ℕ}
    (hw : FullWait k (1 + k * q) ranks h) (hk : 4 ≤ k) (hkr : k + 3 ≤ ranks)
    (hq : 0 < q) (hcard : h.card + 1 = (1 + k * q) + k * m) :
    q * (k - 1) + 2 ≤ m := by
  have hstrict := hw.meld_count_strict_lower hk (by omega) hq hcard
  by_contra hless
  have hm : m = q * (k - 1) + 1 := by omega
  apply hw.card_ne_mul_eye_of_three_extra_ranks hk hkr (by nlinarith)
  rw [hm] at hcard
  have hpred : k - 1 + 1 = k := by omega
  have hprod := congrArg (fun x => k * q * x) hpred
  nlinarith

/-- The low and baseline counts together give a distinct value for each class. -/
private theorem card_le_of_alternate_high_counts {α : Type*} [LinearOrder α]
    (s : Finset α) (t offset : ℕ) (low baseline : α → ℕ)
    (hlow : ∀ i ∈ s, low i < t) (hbase : ∀ i ∈ s, baseline i ≤ t)
    (hpair : ∀ {i j}, i ∈ s → j ∈ s → i < j →
      baseline j ≤ low i ∧ low j < baseline i)
    (hoffset : ∀ i ∈ s, offset ≤ low i + baseline i) :
    s.card ≤ 2 * t - offset := by
  let f (i : ↥s) : Fin (2 * t - offset) :=
    ⟨low i.val + baseline i.val - offset, by
      have := hlow i.val i.property
      have := hbase i.val i.property
      have := hoffset i.val i.property
      omega⟩
  have hdecreasing : StrictAnti f := by
    intro i j hij
    obtain ⟨hl, hh⟩ := hpair i.property j.property hij
    have := hoffset j.val j.property
    change low j.val + baseline j.val - offset < low i.val + baseline i.val - offset
    omega
  simpa using Fintype.card_le_of_injective f hdecreasing.injective

private def highResidueSize (k : ℕ) (h : Multiset ℕ) (r : Fin k) : ℕ :=
  residueSize k (h.filter (k ≤ ·)) r

private theorem highResidueSize_add {k : ℕ} (h g : Multiset ℕ) (r : Fin k) :
    highResidueSize k (h + g) r = highResidueSize k h r + highResidueSize k g r := by
  simp [highResidueSize, Multiset.filter_add, residueSize_add]

private theorem highResidueSize_le {k : ℕ} (h : Multiset ℕ) (r : Fin k) :
    highResidueSize k h r ≤ residueSize k h r :=
  Multiset.count_le_of_le r.val (Multiset.map_le_map (Multiset.filter_le (k ≤ ·) h))

/-- A length-`k` run has a high tile in exactly the residues below its start. -/
private theorem highResidueSize_consecutive {k : ℕ} (start : ℕ) (r : Fin k) :
    highResidueSize k (Multiset.Ico start (start + k)) r = if r.val < start then 1 else 0 := by
  let run := Multiset.Ico start (start + k)
  change highResidueSize k run r = _
  have hle : highResidueSize k run r ≤ 1 :=
    (highResidueSize_le run r).trans_eq (residueSize_consecutive start r)
  by_cases hr : r.val < start
  · rw [ite_eq_left hr]
    by_cases hstart : k ≤ start
    · change residueSize k (run.filter (k ≤ ·)) r = 1
      rw [Multiset.filter_eq_self.mpr (fun x hx => hstart.trans (Multiset.mem_Ico.mp hx).1)]
      exact residueSize_consecutive start r
    · have ht : k + r.val ∈ run.filter (k ≤ ·) := by
        apply Multiset.mem_filter.mpr
        constructor
        · exact Multiset.mem_Ico.mpr ⟨by omega, by omega⟩
        · omega
      have hmod : (k + r.val) % k = r.val := by simp [Nat.mod_eq_of_lt r.isLt]
      have hpos : 0 < highResidueSize k run r :=
        Multiset.count_pos.mpr (Multiset.mem_map.mpr ⟨_, ht, hmod⟩)
      omega
  · rw [ite_eq_right hr]
    by_contra hne
    have hp : 0 < highResidueSize k run r := by omega
    change 0 < ((run.filter (k ≤ ·)).map (· % k)).count r.val at hp
    obtain ⟨tile, ht, hrmod⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp hp)
    rcases Multiset.mem_filter.mp ht with ⟨ht, hhigh⟩
    have hbounds := Multiset.mem_Ico.mp ht
    have hsmall : tile - k < k := by have := r.isLt; omega
    have hmod : tile % k = tile - k := by
      calc
        tile % k = (k + (tile - k)) % k := congrArg (· % k) (by omega)
        _ = tile - k := by simp [Nat.mod_eq_of_lt hsmall]
    omega

private theorem highResidueSize_replicate {k : ℕ} (n tile : ℕ) (r : Fin k) :
    highResidueSize k (Multiset.replicate n tile) r =
      if k ≤ tile ∧ tile % k = r.val then n else 0 := by
  rw [highResidueSize]
  by_cases ht : k ≤ tile
  · rw [Multiset.filter_eq_self.mpr (fun _ hx => Multiset.eq_of_mem_replicate hx ▸ ht)]
    simp [residueSize, ht, Multiset.count_replicate]
  · rw [Multiset.filter_eq_nil.mpr (fun _ hx => Multiset.eq_of_mem_replicate hx ▸ ht)]
    simp [residueSize, ht]

/-- The consecutive melds contribute a common total and an antitone high count
to the residue classes. The identical melds contribute multiples of the meld size. -/
private theorem Melds.exists_high_residue_counts {k : ℕ} {h : Multiset ℕ}
    (hm : Melds k h) :
    ∃ (n : ℕ) (high : Fin k → ℕ), Antitone high ∧ (∀ r, high r ≤ n) ∧
      ∀ r, ∃ a b : ℕ, residueSize k h r = n + k * a ∧
        highResidueSize k h r = high r + k * b := by
  induction hm with
  | empty =>
    exact ⟨0, fun _ => 0, fun _ _ _ => le_rfl, fun _ => le_rfl,
      fun _ => ⟨0, 0, by simp [residueSize], by simp [highResidueSize, residueSize]⟩⟩
  | identical tile _ ih =>
    obtain ⟨n, high, hmono, hle, hcounts⟩ := ih
    refine ⟨n, high, hmono, hle, fun r => ?_⟩
    obtain ⟨a, b, ha, hb⟩ := hcounts r
    refine ⟨a + (if tile % k = r.val then 1 else 0),
      b + (if k ≤ tile ∧ tile % k = r.val then 1 else 0), ?_, ?_⟩
    · rw [residueSize_add, ha]
      simp only [residueSize, Multiset.map_replicate, Multiset.count_replicate]
      split <;> simp_all [Nat.mul_add]
      omega
    · rw [highResidueSize_add, hb, highResidueSize_replicate]
      split <;> simp_all [Nat.mul_add]
      omega
  | consecutive start _ ih =>
    obtain ⟨n, high, hmono, hle, hcounts⟩ := ih
    let bit (r : Fin k) : ℕ := if r.val < start then 1 else 0
    have hbit : Antitone bit := by
      intro i j hij
      have hij' : i.val ≤ j.val := hij
      dsimp [bit]
      split <;> split <;> omega
    refine ⟨n + 1, fun r => high r + bit r, ?_, ?_, fun r => ?_⟩
    · intro i j hij
      exact add_le_add (hmono hij) (hbit hij)
    · intro r
      have hr := hle r
      dsimp [bit]
      split <;> omega
    · obtain ⟨a, b, ha, hb⟩ := hcounts r
      refine ⟨a, b, ?_, ?_⟩
      · rw [residueSize_add, residueSize_consecutive, ha]
        omega
      · rw [highResidueSize_add, highResidueSize_consecutive, hb]
        change bit r + (high r + k * b) = high r + bit r + k * b
        omega

/-- A class with fewer than `k` tiles fixes the number of consecutive melds.
The high-tile counts made by these melds are the high-residue remainders. -/
private theorem Melds.highResidueSize_mod_antitone {k t : ℕ} {h : Multiset ℕ}
    (hm : Melds k h) (r : Fin k) (hr : residueSize k h r = t) (ht : t < k) :
    Antitone (fun i => highResidueSize k h i % k) ∧
      ∀ i, highResidueSize k h i % k ≤ t := by
  obtain ⟨n, high, hmono, hle, hcounts⟩ := hm.exists_high_residue_counts
  obtain ⟨a, _, htotal, _⟩ := hcounts r
  rw [hr] at htotal
  have hn : n ≤ t := by omega
  have hnk : n < k := hn.trans_lt ht
  have hnt : n = t := by
    have hmod := congrArg (· % k) htotal
    simpa [Nat.mod_eq_of_lt hnk, Nat.mod_eq_of_lt ht] using hmod.symm
  subst n
  have heq (i : Fin k) : highResidueSize k h i % k = high i := by
    obtain ⟨_, b, _, hb⟩ := hcounts i
    rw [hb]
    simp [Nat.mod_eq_of_lt ((hle i).trans_lt ht)]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simpa only [heq i, heq j] using hmono hij
  · simpa [heq i] using hle i

/-- A tile with fewer than `k` copies must occur in a consecutive meld. -/
private theorem Melds.exists_remove_consecutive {k : ℕ} {hand : Multiset ℕ}
    (hm : Melds k hand) {tile : ℕ} (hmem : tile ∈ hand) (hcount : hand.count tile < k) :
    ∃ start rest, tile ∈ Multiset.Ico start (start + k) ∧
      hand = Multiset.Ico start (start + k) + rest ∧ Melds k rest := by
  induction hm with
  | empty => simp at hmem
  | @identical rank rest hmrest ih =>
    rcases Multiset.mem_add.mp hmem with hhere | hthere
    · have heq := Multiset.eq_of_mem_replicate hhere
      subst tile
      simp only [Multiset.count_add, Multiset.count_replicate, ite_true] at hcount
      omega
    · have hlt : rest.count tile < k :=
        (Multiset.count_le_of_le tile (by simp)).trans_lt hcount
      obtain ⟨start, other, htile, hrest, hmother⟩ := ih hthere hlt
      refine ⟨start, Multiset.replicate k rank + other, htile, ?_, hmother.identical rank⟩
      rw [hrest]
      ac_rfl
  | @consecutive rank rest hmrest ih =>
    rcases Multiset.mem_add.mp hmem with hhere | hthere
    · exact ⟨rank, rest, hhere, rfl, hmrest⟩
    · have hlt : rest.count tile < k :=
        (Multiset.count_le_of_le tile (by simp)).trans_lt hcount
      obtain ⟨start, other, htile, hrest, hmother⟩ := ih hthere hlt
      refine ⟨start, Multiset.Ico rank (rank + k) + other, htile, ?_, hmother.consecutive rank⟩
      rw [hrest]
      ac_rfl

/-- A tile of rank at least `2k` in a small class forces a high tile in
every residue of the consecutive melds. -/
private theorem Melds.highResidueSize_mod_pos_of_far_tile {k t : ℕ} {hand : Multiset ℕ}
    (hm : Melds k hand) (r : Fin k) (hr : residueSize k hand r = t) (ht : t < k)
    {tile : ℕ} (hres : tile % k = r.val) (hfar : 2 * k ≤ tile) (hmem : tile ∈ hand)
    (s : Fin k) : 0 < highResidueSize k hand s % k := by
  have hc := count_le_residueSize hand r tile hres
  rw [hr] at hc
  obtain ⟨start, rest, htile, hsplit, hmrest⟩ := hm.exists_remove_consecutive hmem (hc.trans_lt ht)
  have hstart : s.val < start := by
    have hbound := (Multiset.mem_Ico.mp htile).2
    have := s.isLt
    omega
  rw [hsplit, residueSize_add, residueSize_consecutive] at hr
  have hsmall : residueSize k rest r < k := by omega
  have hhigh := (hmrest.highResidueSize_mod_antitone r rfl hsmall).2 s
  rw [hsplit, highResidueSize_add, highResidueSize_consecutive, ite_eq_left hstart, Nat.add_mod]
  have hk : 1 < k := by omega
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega : 1 + highResidueSize k rest s % k < k)]
  omega

/-- If the excesses sum to `k*s` and have common remainder `t`, at most
`s-t` classes in any subset have excess above `t`. -/
private theorem card_filter_le_of_residue_excess {k s t : ℕ} (hk : 0 < k)
    (excess : Fin k → ℕ) (hmod : ∀ i, excess i % k = t)
    (htotal : (∑ i, excess i) = k * s) (classes : Finset (Fin k)) :
    t ≤ s ∧ classes.card ≤ (classes.filter (fun i => excess i = t)).card + (s - t) := by
  have hexcess (i : Fin k) : excess i = t + k * (excess i / k) := by
    rw [← hmod i]
    exact (Nat.mod_add_div (excess i) k).symm
  have hmul (u : Finset (Fin k)) :
      (∑ i ∈ u, k * (excess i / k)) = k * (∑ i ∈ u, excess i / k) := by
    induction u using Finset.induction_on with
    | empty => simp
    | @insert i u hi ih => simp [hi, ih, Nat.mul_add]
  have hsum : (∑ i, excess i) = k * (t + ∑ i, excess i / k) := by
    calc
      _ = ∑ i, (t + k * (excess i / k)) := Finset.sum_congr rfl (fun i _ => hexcess i)
      _ = _ := by simp [Finset.sum_add_distrib, hmul, Nat.mul_add]
  have hquot : t + ∑ i, excess i / k = s :=
    Nat.eq_of_mul_eq_mul_left hk (hsum.symm.trans htotal)
  let good := classes.filter (fun i => excess i = t)
  have hbad : (classes \ good).card ≤ ∑ i, excess i / k := by
    calc
      _ = ∑ _ ∈ classes \ good, (1 : ℕ) := by simp
      _ ≤ ∑ i ∈ classes \ good, excess i / k := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        obtain ⟨hmem, hnot⟩ := Finset.mem_sdiff.mp hi
        by_cases hzero : excess i / k = 0
        · have heq : excess i = t := by simpa [hzero] using hexcess i
          exact (hnot (Finset.mem_filter.mpr ⟨hmem, heq⟩)).elim
        · exact Nat.one_le_iff_ne_zero.mpr hzero
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hparts := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun i => excess i = t) classes)
  change (classes \ good).card + good.card = classes.card at hparts
  change t ≤ s ∧ classes.card ≤ good.card + (s - t)
  omega

private theorem residueSize_replicate {k : ℕ} (n tile : ℕ) (r : Fin k) :
    residueSize k (Multiset.replicate n tile) r = if tile % k = r.val then n else 0 := by
  simp [residueSize, Multiset.count_replicate]

/-- Repeated classes of size `p-1+t` have high counts determined by the draw
and the existing eye in its class. -/
private theorem FullWait.exists_high_counts_of_small_residues {h : Multiset ℕ} {q t : ℕ}
    (hw : FullWait k p ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks)
    (hpeq : p = 1 + k * q) (hq : 0 < q) (ht : t < k) (classes : Finset (Fin k))
    (hdraws : ∀ r ∈ classes, k + r.val < ranks)
    (hsize : ∀ r ∈ classes, residueSize k h r = p - 1 + t) :
    ∃ low baseline : Fin k → ℕ,
      (∀ r ∈ classes, low r < t) ∧ (∀ r ∈ classes, baseline r ≤ t) ∧
      (∀ {i j}, i ∈ classes → j ∈ classes → i < j →
        baseline j ≤ low i ∧ low j < baseline i) ∧
      ∀ r ∈ classes, ∀ draw : ℕ, draw < ranks → draw % k = r.val →
        2 * k ≤ draw → ∀ s ∈ classes, s ≠ r → 0 < baseline s := by
  classical
  have hpq : k ≤ k * q := Nat.le_mul_of_pos_right k hq
  have hp : 1 < p := by omega
  have hsmall : p - 1 + t < 2 * (p - 1) := by omega
  have hlowmod (r : Fin k) : r.val % k = r.val := Nat.mod_eq_of_lt r.isLt
  have hhighmod (r : Fin k) : (k + r.val) % k = r.val := by simp [hlowmod r]
  have hanchor_exists (r : Fin k) (hr : r ∈ classes) :
      ∃ eye, eye % k = r.val ∧ p ≤ h.count eye := by
    by_contra! hnone
    have hl := count_draw_of_no_other_eye hw hk hkr r r.val (r.isLt.trans_le hkr) (hlowmod r)
      (fun e he _ => hnone e he)
    have hh := count_draw_of_no_other_eye hw hk hkr r (k + r.val) (hdraws r hr) (hhighmod r)
      (fun e he _ => hnone e he)
    have hpair := count_add_count_le_residueSize h r (hlowmod r) (hhighmod r) (by omega)
    rw [hsize r hr] at hpair
    omega
  let anchor (r : Fin k) : ℕ := if hr : r ∈ classes then Classical.choose (hanchor_exists r hr) else 0
  have hanchor (r : Fin k) (hr : r ∈ classes) :
      anchor r % k = r.val ∧ p ≤ h.count (anchor r) := by
    simpa [anchor, hr] using Classical.choose_spec (hanchor_exists r hr)
  let spare (r : Fin k) := h - Multiset.replicate p (anchor r)
  let low (r : Fin k) := highResidueSize k (spare r) r
  let baseline (r : Fin k) := low r + if k ≤ anchor r then 1 else 0
  have hsplit (r : Fin k) (hr : r ∈ classes) :
      h = Multiset.replicate p (anchor r) + spare r := by
    have hle : Multiset.replicate p (anchor r) ≤ h := by
      rw [Multiset.le_iff_count]
      intro tile
      by_cases he : anchor r = tile
      · subst tile
        simpa [Multiset.count_replicate] using (hanchor r hr).2
      · simp [Multiset.count_replicate, he]
    rw [add_comm]
    exact (Multiset.sub_add_cancel hle).symm
  have hlow (r : Fin k) (hr : r ∈ classes) : low r < t := by
    have heq := congrArg (fun hand => residueSize k hand r) (hsplit r hr)
    simp only [residueSize_add, residueSize_replicate, (hanchor r hr).1, ite_true] at heq
    rw [hsize r hr] at heq
    have hle := highResidueSize_le (spare r) r
    change low r ≤ _ at hle
    omega
  have hbase (r : Fin k) (hr : r ∈ classes) : baseline r ≤ t := by
    have hl := hlow r hr
    dsimp [baseline]
    split <;> omega
  have hhigh (r : Fin k) (hr : r ∈ classes) :
      highResidueSize k h r = (if k ≤ anchor r then p else 0) + low r := by
    have heq := congrArg (fun hand => highResidueSize k hand r) (hsplit r hr)
    simpa only [highResidueSize_add, highResidueSize_replicate, (hanchor r hr).1,
      and_true, low] using heq
  have hbase_mod (r : Fin k) (hr : r ∈ classes) : highResidueSize k h r % k = baseline r := by
    have hb : baseline r < k := (hbase r hr).trans_lt ht
    have heq : highResidueSize k h r = baseline r + k * (if k ≤ anchor r then q else 0) := by
      rw [hhigh r hr]
      dsimp [baseline]
      split <;> simp_all
      omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have hdraw (r : Fin k) (hr : r ∈ classes) (draw : ℕ)
      (hd : draw < ranks) (hdr : draw % k = r.val) :
      ∃ f : Fin k → ℕ, Antitone f ∧ f r = low r + (if k ≤ draw then 1 else 0) ∧
        (∀ s ∈ classes, s ≠ r → f s = baseline s) ∧
        (2 * k ≤ draw → ∀ s, 0 < f s) := by
    obtain ⟨eye, rest, hm, hwin⟩ := hw.2 draw hd
    have heye : eye % k = r.val := (hw.eye_residue hk hkr draw eye hm hwin).trans hdr
    have hcount : p - 1 ≤ h.count eye := by
      have heq := congrArg (fun hand : Multiset ℕ => hand.count eye) hwin
      simp only [Multiset.count_add, Multiset.count_singleton, Multiset.count_replicate,
        ite_true] at heq
      split_ifs at heq <;> omega
    have he : eye = anchor r := by
      by_contra hne
      have hpair := count_add_count_le_residueSize h r heye (hanchor r hr).1 hne
      rw [hsize r hr] at hpair
      have ha := (hanchor r hr).2
      omega
    subst eye
    have hrest : residueSize k rest r = t := by
      have heq := congrArg (fun hand => residueSize k hand r) hwin
      rw [← Multiset.replicate_one] at heq
      simp only [residueSize_add, residueSize_replicate, hdr, (hanchor r hr).1, ite_true] at heq
      rw [hsize r hr] at heq
      omega
    have hanti := (hm.highResidueSize_mod_antitone r hrest ht).1
    refine ⟨fun s => highResidueSize k rest s % k, hanti, ?_, fun s hs hne => ?_, ?_⟩
    · change highResidueSize k rest r % k = _
      have heq := congrArg (fun hand => highResidueSize k hand r) hwin
      rw [← Multiset.replicate_one] at heq
      simp only [highResidueSize_add, highResidueSize_replicate, hdr, (hanchor r hr).1,
        and_true] at heq
      rw [hhigh r hr] at heq
      have hcount : highResidueSize k rest r = low r + (if k ≤ draw then 1 else 0) := by omega
      rw [hcount]
      apply Nat.mod_eq_of_lt
      have hl := hlow r hr
      split <;> omega
    · change highResidueSize k rest s % k = _
      have hval : r.val ≠ s.val := fun he => hne (Fin.ext he.symm)
      have heq := congrArg (fun hand => highResidueSize k hand s) hwin
      rw [← Multiset.replicate_one] at heq
      simp only [highResidueSize_add, highResidueSize_replicate, hdr, (hanchor r hr).1,
        hval, and_false, ite_false, add_zero, zero_add] at heq
      rw [← heq, hbase_mod s hs]
    · intro hfar s
      have hmem : draw ∈ rest := by
        apply Multiset.count_pos.mp
        have heq := congrArg (fun hand : Multiset ℕ => hand.count draw) hwin
        by_cases hsame : anchor r = draw
        · have hc := (hanchor r hr).2
          rw [hsame] at hc
          simp [hsame] at heq
          omega
        · simp [Multiset.count_replicate, hsame] at heq
          omega
      exact hm.highResidueSize_mod_pos_of_far_tile r hrest ht hdr hfar hmem s
  refine ⟨low, baseline, hlow, hbase, ?_, ?_⟩
  · intro i j hi hj hij
    have hihigh : ¬k ≤ i.val := by have := i.isLt; omega
    obtain ⟨f, hanti, hself, hother, _⟩ := hdraw i hi i.val (i.isLt.trans_le hkr) (hlowmod i)
    obtain ⟨g, hanti', hself', hother', _⟩ := hdraw j hj (k + j.val) (hdraws j hj) (hhighmod j)
    have hf := hanti hij.le
    rw [hself, hother j hj hij.ne.symm] at hf
    have hg := hanti' hij.le
    rw [hself', hother' i hi hij.ne] at hg
    simp [hihigh] at hf
    simp at hg
    exact ⟨hf, hg⟩
  · intro r hr draw hd hdr hfar s hs hne
    obtain ⟨f, _, _, hother, hpos⟩ := hdraw r hr draw hd hdr
    simpa only [hother s hs hne] using hpos hfar s

/-- The class excesses above eye capacity have a common remainder
and sum to `k*s` when there are `s` additional melds. -/
private theorem FullWait.exists_residue_excesses {h : Multiset ℕ} {q s : ℕ}
    (hw : FullWait k (1 + k * q) ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks)
    (hcard : h.card + 1 = (1 + k * q) + k * (q * (k - 1) + s)) :
    ∃ (excess : Fin k → ℕ) (t : ℕ), (∀ r, excess r + k * q = residueSize k h r) ∧
      (∑ r, excess r) = k * s ∧ t < k ∧ ∀ r, excess r % k = t := by
  have hkpos : 0 < k := by omega
  have hcard' : h.card = k * (k * q) + k * s := by
    have hpred : k - 1 + 1 = k := by omega
    have hprod := congrArg (fun x => k * q * x) hpred
    rw [Nat.mul_add k (q * (k - 1)) s] at hcard
    nlinarith
  let excess (r : Fin k) := residueSize k h r - k * q
  have hadd (r : Fin k) : excess r + k * q = residueSize k h r := by
    apply Nat.sub_add_cancel
    simpa using hw.residueSize_lower hk hkr r
  have hsum : (∑ r : Fin k, excess r) + k * (k * q) = h.card := by
    calc
      _ = ∑ r : Fin k, (excess r + k * q) := by simp [Finset.sum_add_distrib]
      _ = _ := by simp [hadd, sum_residueSize hkpos]
  have htotal : (∑ r : Fin k, excess r) = k * s := by omega
  let zero : Fin k := ⟨0, hkpos⟩
  let t := excess zero % k
  have ht : t < k := Nat.mod_lt _ hkpos
  have hmod (r : Fin k) : excess r % k = t := by
    have hcongr : (residueSize k h r : ZMod k) = (residueSize k h zero : ZMod k) :=
      (hw.obstruction hk hkr).2 r zero
    have hcast : (excess r : ZMod k) = (excess zero : ZMod k) := by
      apply add_right_cancel (b := ((k * q : ℕ) : ZMod k))
      simpa only [← Nat.cast_add, hadd] using hcongr
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hcast
  exact ⟨excess, t, hadd, htotal, ht, hmod⟩

/-- Each pair of repeated residue classes requires one meld above the capacity bound.
A remaining unpaired class requires one more. -/
theorem FullWait.meld_count_lower_with_repeated_residues {h : Multiset ℕ} {q m : ℕ}
    (hw : FullWait k (1 + k * q) ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks)
    (hq : 0 < q) (hcard : h.card + 1 = (1 + k * q) + k * m) :
    q * (k - 1) + (min (ranks - k) k + 1) / 2 ≤ m := by
  let d := min (ranks - k) k
  change q * (k - 1) + (d + 1) / 2 ≤ m
  by_contra! hfail
  have hkpos : 0 < k := by omega
  have hd : d ≤ k := min_le_right _ _
  have hdk : d ≤ ranks - k := min_le_left _ _
  let s := m - q * (k - 1)
  have hcap := hw.meld_count_lower hk hkr hcard
  have hm : m = q * (k - 1) + s := by dsimp [s]; omega
  have hs : 2 * s < d := by omega
  rw [hm] at hcard
  obtain ⟨excess, t, hadd, htotal, ht, hmod⟩ := hw.exists_residue_excesses hk hkr hcard
  let repeated := (Finset.univ : Finset (Fin d)).map (Fin.castLEEmb hd)
  have hrd : repeated.card = d := by simp [repeated]
  have hdraws (r : Fin k) (hr : r ∈ repeated) : k + r.val < ranks := by
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hr
    rw [← hi]
    change k + i.val < ranks
    have := i.isLt
    omega
  let good := repeated.filter (fun r => excess r = t)
  obtain ⟨hts, hbudget⟩ := card_filter_le_of_residue_excess hkpos excess hmod htotal repeated
  change repeated.card ≤ good.card + (s - t) at hbudget
  have hgoodDraw (r : Fin k) (hr : r ∈ good) : k + r.val < ranks :=
    hdraws r (Finset.mem_filter.mp hr).1
  have hgoodSize (r : Fin k) (hr : r ∈ good) : residueSize k h r = 1 + k * q - 1 + t := by
    have he := (Finset.mem_filter.mp hr).2
    rw [← hadd r, he]
    omega
  obtain ⟨low, baseline, hlow, hbase, hpair, _⟩ :=
    hw.exists_high_counts_of_small_residues hk hkr rfl hq ht good hgoodDraw hgoodSize
  have hgood : good.card ≤ 2 * t := by
    simpa using card_le_of_alternate_high_counts good t 0 low baseline hlow hbase hpair
      (fun _ _ => Nat.zero_le _)
  omega

/-- For even `k`, the first rank beyond `2k` forces another meld. -/
theorem FullWait.meld_count_lower_even_beyond_twice {h : Multiset ℕ} {q m : ℕ}
    (hw : FullWait k (1 + k * q) ranks h) (hk : 4 ≤ k) (heven : k % 2 = 0)
    (hranks : 2 * k < ranks) (hq : 0 < q)
    (hcard : h.card + 1 = (1 + k * q) + k * m) :
    q * (k - 1) + k / 2 + 1 ≤ m := by
  by_contra! hfail
  have hkr : k ≤ ranks := by omega
  have hkpos : 0 < k := by omega
  have hmin : min (ranks - k) k = k := min_eq_right (by omega)
  have hbound := hw.meld_count_lower_with_repeated_residues hk hkr hq hcard
  rw [hmin] at hbound
  have hm : m = q * (k - 1) + k / 2 := by omega
  rw [hm] at hcard
  obtain ⟨excess, t, hadd, htotal, ht, hmod⟩ := hw.exists_residue_excesses hk hkr hcard
  let good := (Finset.univ : Finset (Fin k)).filter (fun r => excess r = t)
  obtain ⟨hts, hbudget⟩ :=
    card_filter_le_of_residue_excess hkpos excess hmod htotal (Finset.univ : Finset (Fin k))
  have hcount : k ≤ good.card + (k / 2 - t) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hbudget
  have hgoodSize (r : Fin k) (hr : r ∈ good) : residueSize k h r = 1 + k * q - 1 + t := by
    have he := (Finset.mem_filter.mp hr).2
    rw [← hadd r, he]
    omega
  have hdraws (r : Fin k) : k + r.val < ranks := by have := r.isLt; omega
  obtain ⟨low, baseline, hlow, hbase, hpair, hfar⟩ :=
    hw.exists_high_counts_of_small_residues hk hkr rfl hq ht good
      (fun r _ => hdraws r) hgoodSize
  have hgood : good.card ≤ 2 * t := by
    simpa using card_le_of_alternate_high_counts good t 0 low baseline hlow hbase hpair
      (fun _ _ => Nat.zero_le _)
  have htk : 2 * t = k := by omega
  have hcardGood : k ≤ good.card := by omega
  have hfull : good = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using hcardGood)
  let zero : Fin k := ⟨0, hkpos⟩
  let last : Fin k := ⟨k - 1, by omega⟩
  have hz : zero ∈ good := by simp [hfull]
  have hl : last ∈ good := by simp [hfull]
  have hne : last ≠ zero := by
    intro he
    have hval := congrArg Fin.val he
    change k - 1 = 0 at hval
    omega
  have hlast : 0 < baseline last :=
    hfar zero hz (2 * k) hranks (by simp [zero]) le_rfl last hl hne
  have hoffset (i : Fin k) (hi : i ∈ good) : 1 ≤ low i + baseline i := by
    by_cases he : i = last
    · subst i
      omega
    · have hilast : i < last := by
        apply lt_of_le_of_ne _ he
        change i.val ≤ k - 1
        have := i.isLt
        omega
      have hilow := (hpair hi hl hilast).1
      omega
  have hstrict := card_le_of_alternate_high_counts good t 1 low baseline hlow hbase hpair hoffset
  omega

/-- The periodic construction attains the exact minimum from `k` to `2k` ranks. -/
theorem minimum_meld_count_of_le_twice {q : ℕ} (hk : 4 ≤ k) (hq : 0 < q)
    (hkr : k ≤ ranks) (hranks : ranks ≤ 2 * k) :
    let minimum := q * (k - 1) + (ranks - k + 1) / 2
    (∃ h : Multiset ℕ, FullWait k (1 + k * q) ranks h ∧
      h.card + 1 = (1 + k * q) + k * minimum) ∧
    ∀ (h : Multiset ℕ) (m : ℕ), FullWait k (1 + k * q) ranks h →
      h.card + 1 = (1 + k * q) + k * m → minimum ≤ m := by
  dsimp only
  have hl : ranks - k ≤ k := by omega
  have hm : periodicMeldCount k q ranks = q * (k - 1) + (ranks - k + 1) / 2 := by
    rcases lt_or_eq_of_le hl with hlt | heq
    · simp [periodicMeldCount, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
    · simp [periodicMeldCount, heq, Nat.div_self (by omega : 0 < k)]
  constructor
  · simpa only [hm] using exists_fullWait_periodic q (by omega) hkr
  · intro h m hw hcard
    simpa only [min_eq_left hl] using hw.meld_count_lower_with_repeated_residues hk hkr hq hcard

/-- Even meld sizes attain the next minimum at both `2k+1` and `2k+2` ranks. -/
theorem minimum_meld_count_even_beyond_twice {q : ℕ} (hk : 4 ≤ k) (hq : 0 < q)
    (heven : k % 2 = 0) (hranks : 2 * k < ranks) (hupper : ranks ≤ 2 * k + 2) :
    let minimum := q * (k - 1) + k / 2 + 1
    (∃ h : Multiset ℕ, FullWait k (1 + k * q) ranks h ∧
      h.card + 1 = (1 + k * q) + k * minimum) ∧
    ∀ (h : Multiset ℕ) (m : ℕ), FullWait k (1 + k * q) ranks h →
      h.card + 1 = (1 + k * q) + k * m → minimum ≤ m := by
  dsimp only
  have hkr : k ≤ ranks := by omega
  have hm : periodicMeldCount k q ranks = q * (k - 1) + k / 2 + 1 := by
    rw [periodicMeldCount_even k q ranks heven]
    omega
  constructor
  · simpa only [hm] using exists_fullWait_periodic q (by omega) hkr
  · intro h m hw hcard
    exact hw.meld_count_lower_even_beyond_twice hk heven hranks hq hcard

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
  have hcount : (ranks - k + 1) / 2 = if ranks = k then 0 else 1 := by
    split <;> omega
  simpa only [hcount] using minimum_meld_count_of_le_twice hk hq hkr (by omega)

/-- The periodic construction attains the minimum for three or four extra ranks. -/
theorem minimum_meld_count_three_or_four_extra {q extra : ℕ} (hk : 4 ≤ k) (hq : 0 < q)
    (hextra : 3 ≤ extra) (hupper : extra ≤ 4) :
    (∃ h : Multiset ℕ, FullWait k (1 + k * q) (k + extra) h ∧
      h.card + 1 = (1 + k * q) + k * (q * (k - 1) + 2)) ∧
    ∀ (h : Multiset ℕ) (m : ℕ), FullWait k (1 + k * q) (k + extra) h →
      h.card + 1 = (1 + k * q) + k * m → q * (k - 1) + 2 ≤ m := by
  have hcount : (extra + 1) / 2 = 2 := by omega
  simpa only [Nat.add_sub_cancel_left, hcount] using
    minimum_meld_count_of_le_twice (ranks := k + extra) hk hq (by omega) (by omega)

end MeldSizeObstruction
