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

/-- Counts the tiles at or above the upper endpoint of a draw pair, in its residue. -/
private def drawPairHighCount (k a : ℕ) (hand : Multiset ℕ) : ℕ :=
  ((hand.filter (a + k ≤ ·)).map (· % k)).count (a % k)

private theorem drawPairHighCount_add (k a : ℕ) (h g : Multiset ℕ) :
    drawPairHighCount k a (h + g) = drawPairHighCount k a h + drawPairHighCount k a g := by
  simp [drawPairHighCount, Multiset.filter_add]

private theorem drawPairHighCount_replicate (k a n tile : ℕ) :
    drawPairHighCount k a (Multiset.replicate n tile) =
      if a + k ≤ tile ∧ tile % k = a % k then n else 0 := by
  rw [drawPairHighCount]
  by_cases ht : a + k ≤ tile
  · rw [Multiset.filter_eq_self.mpr (fun _ hx => Multiset.eq_of_mem_replicate hx ▸ ht)]
    simp [ht, Multiset.count_replicate]
  · rw [Multiset.filter_eq_nil.mpr (fun _ hx => Multiset.eq_of_mem_replicate hx ▸ ht)]
    simp [ht]

/-- A run contributes to a draw pair's high count precisely when its start is
above the pair's lower endpoint. -/
private theorem drawPairHighCount_consecutive {k : ℕ} (hk : 0 < k) (a start : ℕ) :
    drawPairHighCount k a (Multiset.Ico start (start + k)) = if a < start then 1 else 0 := by
  let run := Multiset.Ico start (start + k)
  change drawPairHighCount k a run = _
  have hfull : (run.map (· % k)).count (a % k) = 1 :=
    residueSize_consecutive start ⟨a % k, Nat.mod_lt _ hk⟩
  have hle : drawPairHighCount k a run ≤ 1 := by
    rw [← hfull]
    exact Multiset.count_le_of_le _ (Multiset.map_le_map (Multiset.filter_le (a + k ≤ ·) run))
  by_cases hs : a < start
  · rw [ite_eq_left hs]
    have hpos : 0 < (run.map (· % k)).count (a % k) := by rw [hfull]; decide
    obtain ⟨tile, hmem, hres⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp hpos)
    have hlt := hs.trans_le (Multiset.mem_Ico.mp hmem).1
    have hdvd : k ∣ tile - a := (Nat.modEq_iff_dvd' hlt.le).mp hres.symm
    have hdist : k ≤ tile - a := Nat.le_of_dvd (by omega) hdvd
    have hm : 0 < drawPairHighCount k a run :=
      Multiset.count_pos.mpr (Multiset.mem_map.mpr
        ⟨tile, Multiset.mem_filter.mpr ⟨hmem, by omega⟩, hres⟩)
    omega
  · rw [ite_eq_right hs, drawPairHighCount]
    have hzero : run.filter (a + k ≤ ·) = 0 := by
      apply Multiset.filter_eq_nil.mpr
      intro tile hmem
      have hlt := (Multiset.mem_Ico.mp hmem).2
      omega
    simp [hzero]

/-- The runs contribute a common residue total and a decreasing high count
across draw pairs. Identical melds contribute multiples of the meld size. -/
private theorem Melds.exists_drawPair_counts {k : ℕ} {hand : Multiset ℕ} (hm : Melds k hand)
    (hk : 0 < k) :
    ∃ (n : ℕ) (high : ℕ → ℕ), Antitone high ∧ (∀ a, high a ≤ n) ∧
      (∀ r : Fin k, ∃ c, residueSize k hand r = n + k * c) ∧
      ∀ a, ∃ c, drawPairHighCount k a hand = high a + k * c := by
  induction hm with
  | empty =>
    exact ⟨0, fun _ => 0, fun _ _ _ => le_rfl, fun _ => le_rfl,
      fun _ => ⟨0, by simp [residueSize]⟩, fun _ => ⟨0, by simp [drawPairHighCount]⟩⟩
  | identical tile _ ih =>
    obtain ⟨n, high, hanti, hle, hres, hhigh⟩ := ih
    refine ⟨n, high, hanti, hle, ?_, ?_⟩
    · intro r
      obtain ⟨c, hc⟩ := hres r
      refine ⟨c + (if tile % k = r.val then 1 else 0), ?_⟩
      rw [residueSize_add, hc]
      simp only [residueSize, Multiset.map_replicate, Multiset.count_replicate]
      split <;> simp_all [Nat.mul_add]
      omega
    · intro a
      obtain ⟨c, hc⟩ := hhigh a
      refine ⟨c + (if a + k ≤ tile ∧ tile % k = a % k then 1 else 0), ?_⟩
      rw [drawPairHighCount_add, drawPairHighCount_replicate, hc]
      split <;> simp_all [Nat.mul_add]
      omega
  | consecutive start _ ih =>
    obtain ⟨n, high, hanti, hle, hres, hhigh⟩ := ih
    let included (a : ℕ) := if a < start then 1 else 0
    have hinc : Antitone included := by
      intro a b hab
      dsimp [included]
      split <;> split <;> omega
    refine ⟨n + 1, fun a => high a + included a, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      exact add_le_add (hanti hab) (hinc hab)
    · intro a
      have ha := hle a
      dsimp [included]
      split <;> omega
    · intro r
      obtain ⟨c, hc⟩ := hres r
      refine ⟨c, ?_⟩
      rw [residueSize_add, residueSize_consecutive, hc]
      omega
    · intro a
      obtain ⟨c, hc⟩ := hhigh a
      refine ⟨c, ?_⟩
      rw [drawPairHighCount_add, drawPairHighCount_consecutive hk, hc]
      change included a + (high a + k * c) = high a + included a + k * c
      omega

/-- A small residue class fixes the run count and makes the high-count
remainders antitone across the ordered draw pairs. -/
private theorem Melds.drawPairHighCount_mod_antitone {k t : ℕ} {hand : Multiset ℕ}
    (hm : Melds k hand) (r : Fin k) (hr : residueSize k hand r = t) (ht : t < k) :
    Antitone (fun a => drawPairHighCount k a hand % k) ∧
      ∀ a, drawPairHighCount k a hand % k ≤ t := by
  obtain ⟨n, high, hanti, hle, hres, hhigh⟩ := hm.exists_drawPair_counts (by omega)
  obtain ⟨c, hc⟩ := hres r
  rw [hr] at hc
  have hn : n < k := by omega
  have hnt : n = t := by
    have hmod := congrArg (· % k) hc
    simpa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt ht] using hmod.symm
  subst n
  have heq (a : ℕ) : drawPairHighCount k a hand % k = high a := by
    obtain ⟨b, hb⟩ := hhigh a
    rw [hb, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ((hle a).trans_lt ht)]
  exact ⟨fun a b hab => by simpa only [heq] using hanti hab, fun a => by rw [heq]; exact hle a⟩

/-- Any other residue occurs strictly between two ordered ranks in one residue. -/
private theorem exists_between_of_same_residue {k a b z : ℕ} (hk : 0 < k) (hab : a < b)
    (hsame : a % k = b % k) (hdiff : a % k ≠ z % k) :
    ∃ c, a < c ∧ c < b ∧ c % k = z % k := by
  have hdvd : k ∣ b - a := (Nat.modEq_iff_dvd' hab.le).mp hsame
  have hgap : k ≤ b - a := Nat.le_of_dvd (by omega) hdvd
  let run := Multiset.Ico (a + 1) (a + 1 + k)
  have hcount : (run.map (· % k)).count (z % k) = 1 :=
    residueSize_consecutive (a + 1) ⟨z % k, Nat.mod_lt _ hk⟩
  have hpos : 0 < (run.map (· % k)).count (z % k) := by rw [hcount]; decide
  obtain ⟨c, hc, hres⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp hpos)
  have hcne : c ≠ a + k := by
    intro he
    rw [he] at hres
    exact hdiff (by simpa using hres)
  have hbounds := Multiset.mem_Ico.mp hc
  exact ⟨c, by omega, by omega, hres⟩

/-- In the first two blocks of ranks, more than two ranks cannot all lie in
one residue. -/
private theorem exists_ne_residue_of_two_lt_card {k : ℕ} (hk : 0 < k) (ranks : Finset ℕ)
    (hbound : ∀ a ∈ ranks, a < 2 * k) (hcard : 2 < ranks.card) (r : ℕ) :
    ∃ a ∈ ranks, a % k ≠ r := by
  by_contra! hsame
  let f (a : ↥ranks) : Fin 2 :=
    ⟨a.val / k, (Nat.div_lt_iff_lt_mul hk).mpr (hbound a.val a.property)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hquot : i.val / k = j.val / k := congrArg Fin.val hij
    apply Subtype.ext
    calc
      i.val = i.val % k + k * (i.val / k) := (Nat.mod_add_div _ _).symm
      _ = j.val % k + k * (j.val / k) := by
        rw [hsame i.val i.property, hsame j.val j.property, hquot]
      _ = j.val := Nat.mod_add_div _ _
  have hle : ranks.card ≤ 2 := by simpa using Fintype.card_le_of_injective f hf
  omega

/-- Comparing the low and high draws in different residues bounds the number
of pairs, even when one residue contains two pairs. -/
private theorem card_le_twice_of_drawPair_counts {k t L : ℕ} (hk : 0 < k) (ht : 0 < t)
    (hL : L ≤ 2 * k) (pairs : Finset ℕ) (hbound : ∀ a ∈ pairs, a < L)
    (hclosed : ∀ {a b}, a ∈ pairs → b < L → a % k = b % k → b ∈ pairs)
    (low base : ℕ → ℕ) (hlow : ∀ a ∈ pairs, low a < t) (hbase : ∀ a ∈ pairs, base a ≤ t)
    (hpair : ∀ {a b}, a ∈ pairs → b ∈ pairs → a < b → a % k ≠ b % k →
      base b ≤ low a ∧ low b < base a) :
    pairs.card ≤ 2 * t := by
  by_contra! hcard
  have htwo : 2 < pairs.card := by omega
  have hdecreasing_of_ne {a b : ℕ} (ha : a ∈ pairs) (hb : b ∈ pairs)
      (hab : a < b) (hdiff : a % k ≠ b % k) : low b + base b < low a + base a := by
    obtain ⟨hlo, hhi⟩ := hpair ha hb hab hdiff
    omega
  let f (a : ↥pairs) : Fin (2 * t) :=
    ⟨low a.val + base a.val, by
      have := hlow a.val a.property
      have := hbase a.val a.property
      omega⟩
  have hdecreasing : StrictAnti f := by
    intro a b hab
    change a.val < b.val at hab
    change low b.val + base b.val < low a.val + base a.val
    by_cases hsame : a.val % k = b.val % k
    · obtain ⟨z, hz, hzres⟩ := exists_ne_residue_of_two_lt_card hk pairs
        (fun z hz => (hbound z hz).trans_le hL) htwo (a.val % k)
      obtain ⟨c, hac, hcb, hcres⟩ := exists_between_of_same_residue hk hab hsame hzres.symm
      have hc := hclosed hz (hcb.trans (hbound b.val b.property)) hcres.symm
      have hacres : a.val % k ≠ c % k := by simpa only [hcres] using hzres.symm
      have hcbres : c % k ≠ b.val % k := by rwa [hcres, ← hsame]
      exact (hdecreasing_of_ne hc b.property hcb hcbres).trans
        (hdecreasing_of_ne a.property hc hac hacres)
    · exact hdecreasing_of_ne a.property b.property hab hsame
  have hle : pairs.card ≤ 2 * t := by
    simpa using Fintype.card_le_of_injective f hdecreasing.injective
  omega

/-- Each exceptional residue can remove at most two pairs in the first two
blocks of draw-pair indices. -/
private theorem card_filter_le_of_drawPair_excess {k s t L : ℕ} (hk : 0 < k) (hL : L ≤ 2 * k)
    (excess : Fin k → ℕ) (hmod : ∀ i, excess i % k = t)
    (htotal : (∑ i, excess i) = k * s) :
    t ≤ s ∧ L ≤ ((Finset.range L).filter (fun a => excess (rankResidue hk a) = t)).card +
      2 * (s - t) := by
  let all := Finset.range L
  let good := all.filter (fun a => excess (rankResidue hk a) = t)
  let bad := all \ good
  have hbound (a : ℕ) (ha : a ∈ bad) : a < L := Finset.mem_range.mp (Finset.mem_sdiff.mp ha).1
  have hnot_good (a : ℕ) (ha : a ∈ bad) : excess (rankResidue hk a) ≠ t := by
    intro he
    exact (Finset.mem_sdiff.mp ha).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ha).1, he⟩)
  have hcap (u : Finset ℕ) (hu : u ⊆ bad) (hinj : Set.InjOn (rankResidue hk) ↑u) :
      u.card ≤ s - t := by
    let image := u.image (rankResidue hk)
    have hempty : image.filter (fun r => excess r = t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨him, hgood⟩ := Finset.mem_filter.mp hr
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp him
      exact hnot_good a (hu ha) hgood
    have hbudget := (card_filter_le_of_residue_excess hk excess hmod htotal image).2
    rw [hempty, Finset.card_empty, zero_add] at hbudget
    have himage : image.card = u.card := Finset.card_image_of_injOn hinj
    omega
  let lower := bad.filter (fun a => a < k)
  let upper := bad.filter (fun a => k ≤ a)
  have hlower : lower.card ≤ s - t := by
    apply hcap lower (Finset.filter_subset _ _)
    intro a ha b hb he
    have hka := (Finset.mem_filter.mp ha).2
    have hkb := (Finset.mem_filter.mp hb).2
    have hval := congrArg Fin.val he
    change a % k = b % k at hval
    simpa only [Nat.mod_eq_of_lt hka, Nat.mod_eq_of_lt hkb] using hval
  have hmod_upper {a : ℕ} (ha : a ∈ upper) : a % k = a - k := by
    obtain ⟨ha, hka⟩ := Finset.mem_filter.mp ha
    have hal := hbound a ha
    have ha' : a - k < k := by omega
    calc
      a % k = (k + (a - k)) % k := congrArg (· % k) (by omega)
      _ = a - k := by simp [Nat.mod_eq_of_lt ha']
  have hupper : upper.card ≤ s - t := by
    apply hcap upper (Finset.filter_subset _ _)
    intro a ha b hb he
    have hka := (Finset.mem_filter.mp ha).2
    have hkb := (Finset.mem_filter.mp hb).2
    have hval := congrArg Fin.val he
    change a % k = b % k at hval
    rw [hmod_upper ha, hmod_upper hb] at hval
    omega
  have hparts : lower.card + upper.card = bad.card := by
    simpa only [lower, upper, not_lt] using
      Finset.card_filter_add_card_filter_not (s := bad) (fun a => a < k)
  have hsplit : bad.card + good.card = L := by
    simpa only [bad, good, all, Finset.card_range] using
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun a => excess (rankResidue hk a) = t) all)
  have hts := (card_filter_le_of_residue_excess hk excess hmod htotal Finset.univ).1
  change t ≤ s ∧ L ≤ good.card + 2 * (s - t)
  omega

/-- For small classes, a low or high draw fixes the high count of its pair.
A draw in another class keeps the baseline count unchanged. -/
private theorem FullWait.exists_drawPair_high_counts {h : Multiset ℕ} {q t : ℕ}
    (hw : FullWait k p ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks)
    (hpeq : p = 1 + k * q) (hq : 0 < q) (ht : t < k) (pairs : Finset ℕ)
    (hdraws : ∀ a ∈ pairs, a + k < ranks)
    (hsize : ∀ a ∈ pairs, residueSize k h (rankResidue (by omega : 0 < k) a) = p - 1 + t) :
    ∃ anchor low base : ℕ → ℕ,
      (∀ a ∈ pairs, anchor a % k = a % k ∧ p ≤ h.count (anchor a)) ∧
      (∀ a ∈ pairs, base a = low a + if a + k ≤ anchor a then 1 else 0) ∧
      (∀ a ∈ pairs, low a < t) ∧ (∀ a ∈ pairs, base a ≤ t) ∧
      ∀ {a b}, a ∈ pairs → b ∈ pairs → a < b → a % k ≠ b % k →
        base b ≤ low a ∧ low b < base a := by
  classical
  have hkpos : 0 < k := by omega
  let r (a : ℕ) := rankResidue hkpos a
  have hpq : k ≤ k * q := Nat.le_mul_of_pos_right k hq
  have hp : 1 < p := by omega
  have hsmall : p - 1 + t < 2 * (p - 1) := by omega
  have hdrawLow (a : ℕ) (ha : a ∈ pairs) : a < ranks := by have := hdraws a ha; omega
  have hdrawMod (a : ℕ) : (a + k) % k = a % k := by simp
  have hanchor_exists (a : ℕ) (ha : a ∈ pairs) :
      ∃ eye, eye % k = a % k ∧ p ≤ h.count eye := by
    by_contra! hnone
    have hl := count_draw_of_no_other_eye hw hk hkr (r a) a (hdrawLow a ha) rfl
      (fun eye he _ => hnone eye he)
    have hh := count_draw_of_no_other_eye hw hk hkr (r a) (a + k) (hdraws a ha) (hdrawMod a)
      (fun eye he _ => hnone eye he)
    have hpair := count_add_count_le_residueSize h (r a) rfl (hdrawMod a) (by omega)
    change _ ≤ residueSize k h (rankResidue hkpos a) at hpair
    rw [hsize a ha] at hpair
    omega
  let anchor (a : ℕ) := if ha : a ∈ pairs then Classical.choose (hanchor_exists a ha) else 0
  have hanchor (a : ℕ) (ha : a ∈ pairs) :
      anchor a % k = a % k ∧ p ≤ h.count (anchor a) := by
    simpa [anchor, ha] using Classical.choose_spec (hanchor_exists a ha)
  let spare (a : ℕ) := h - Multiset.replicate p (anchor a)
  let low (a : ℕ) := drawPairHighCount k a (spare a)
  let base (a : ℕ) := low a + if a + k ≤ anchor a then 1 else 0
  have hsplit (a : ℕ) (ha : a ∈ pairs) :
      h = Multiset.replicate p (anchor a) + spare a := by
    have hle : Multiset.replicate p (anchor a) ≤ h := by
      rw [Multiset.le_iff_count]
      intro tile
      by_cases he : anchor a = tile
      · subst tile
        simpa [Multiset.count_replicate] using (hanchor a ha).2
      · simp [Multiset.count_replicate, he]
    rw [add_comm]
    exact (Multiset.sub_add_cancel hle).symm
  have hlow (a : ℕ) (ha : a ∈ pairs) : low a < t := by
    have heq := congrArg (fun hand => residueSize k hand (r a)) (hsplit a ha)
    have heye : anchor a % k = (r a).val := (hanchor a ha).1
    simp only [residueSize_add, residueSize_replicate, heye, ite_true] at heq
    change residueSize k h (rankResidue hkpos a) = _ at heq
    rw [hsize a ha] at heq
    have hle : low a ≤ residueSize k (spare a) (r a) :=
      Multiset.count_le_of_le _ (Multiset.map_le_map (Multiset.filter_le (a + k ≤ ·) (spare a)))
    omega
  have hbase (a : ℕ) (ha : a ∈ pairs) : base a ≤ t := by
    have hl := hlow a ha
    dsimp [base]
    split <;> omega
  have hhigh (a : ℕ) (ha : a ∈ pairs) :
      drawPairHighCount k a h = (if a + k ≤ anchor a then p else 0) + low a := by
    have heq := congrArg (drawPairHighCount k a) (hsplit a ha)
    simpa only [drawPairHighCount_add, drawPairHighCount_replicate, (hanchor a ha).1,
      and_true, low] using heq
  have hbaseMod (a : ℕ) (ha : a ∈ pairs) : drawPairHighCount k a h % k = base a := by
    have hb := (hbase a ha).trans_lt ht
    have heq : drawPairHighCount k a h = base a + k * (if a + k ≤ anchor a then q else 0) := by
      rw [hhigh a ha]
      dsimp [base]
      split <;> simp_all
      omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have hdraw (a : ℕ) (ha : a ∈ pairs) (draw : ℕ)
      (hd : draw < ranks) (hdr : draw % k = a % k) :
      ∃ f : ℕ → ℕ, Antitone f ∧ f a = low a + (if a + k ≤ draw then 1 else 0) ∧
        ∀ b ∈ pairs, a % k ≠ b % k → f b = base b := by
    obtain ⟨eye, rest, hm, hwin⟩ := hw.2 draw hd
    have heye : eye % k = a % k := (hw.eye_residue hk hkr draw eye hm hwin).trans hdr
    have hcount : p - 1 ≤ h.count eye := by
      have heq := congrArg (fun hand : Multiset ℕ => hand.count eye) hwin
      simp only [Multiset.count_add, Multiset.count_singleton, Multiset.count_replicate,
        ite_true] at heq
      split_ifs at heq <;> omega
    have he : eye = anchor a := by
      by_contra hne
      have hpair := count_add_count_le_residueSize h (r a) heye (hanchor a ha).1 hne
      change _ ≤ residueSize k h (rankResidue hkpos a) at hpair
      rw [hsize a ha] at hpair
      have hanchorCount := (hanchor a ha).2
      omega
    subst eye
    have hrest : residueSize k rest (r a) = t := by
      have heq := congrArg (fun hand => residueSize k hand (r a)) hwin
      rw [← Multiset.replicate_one] at heq
      have hdrawRes : draw % k = (r a).val := hdr
      have heyeRes : anchor a % k = (r a).val := (hanchor a ha).1
      simp only [residueSize_add, residueSize_replicate, hdrawRes, heyeRes, ite_true] at heq
      change residueSize k h (rankResidue hkpos a) + 1 = _ at heq
      rw [hsize a ha] at heq
      omega
    have hanti := (hm.drawPairHighCount_mod_antitone (r a) hrest ht).1
    refine ⟨fun b => drawPairHighCount k b rest % k, hanti, ?_, fun b hb hdiff => ?_⟩
    · change drawPairHighCount k a rest % k = _
      have heq := congrArg (drawPairHighCount k a) hwin
      rw [← Multiset.replicate_one] at heq
      simp only [drawPairHighCount_add, drawPairHighCount_replicate, hdr, (hanchor a ha).1,
        and_true] at heq
      rw [hhigh a ha] at heq
      have hcount : drawPairHighCount k a rest = low a + (if a + k ≤ draw then 1 else 0) := by omega
      rw [hcount]
      apply Nat.mod_eq_of_lt
      have hl := hlow a ha
      split <;> omega
    · change drawPairHighCount k b rest % k = _
      have heq := congrArg (drawPairHighCount k b) hwin
      rw [← Multiset.replicate_one] at heq
      simp only [drawPairHighCount_add, drawPairHighCount_replicate, hdr, (hanchor a ha).1,
        hdiff, and_false, ite_false, add_zero, zero_add] at heq
      rw [← heq, hbaseMod b hb]
  refine ⟨anchor, low, base, hanchor, fun _ _ => rfl, hlow, hbase, ?_⟩
  intro a b ha hb hab hdiff
  have halow : ¬a + k ≤ a := by omega
  obtain ⟨f, hanti, hself, hother⟩ := hdraw a ha a (hdrawLow a ha) rfl
  obtain ⟨g, hanti', hself', hother'⟩ := hdraw b hb (b + k) (hdraws b hb) (hdrawMod b)
  have hf := hanti hab.le
  rw [hself, hother b hb hdiff] at hf
  have hg := hanti' hab.le
  rw [hself', hother' a ha hdiff.symm] at hg
  simp [halow] at hf
  simp at hg
  exact ⟨hf, hg⟩

private theorem tight_pair_counts {t : ℕ} (low base : ℕ → ℕ)
    (hlow : ∀ i < 2 * t, low i < t) (hbase : ∀ i < 2 * t, base i ≤ t)
    (hflag : ∀ i < 2 * t, low i ≤ base i ∧ base i ≤ low i + 1)
    (hpair : ∀ i, i + 1 < 2 * t → base (i + 1) ≤ low i ∧ low (i + 1) < base i) :
    ∀ i < 2 * t, base i = t - (i + 1) / 2 ∧ low i = t - 1 - i / 2 := by
  let f (i : ℕ) := low i + base i + i
  have hf (i : ℕ) (hi : i + 1 < 2 * t) : f (i + 1) ≤ f i := by
    obtain ⟨h₁, h₂⟩ := hpair i hi
    dsimp [f]
    omega
  have hanti (a b : ℕ) (hab : a ≤ b) (hb : b < 2 * t) : f b ≤ f a := by
    induction b with
    | zero =>
      have : a = 0 := by omega
      subst a
      exact le_rfl
    | succ b ih =>
      by_cases h : a = b + 1
      · subst a
        exact le_rfl
      · exact (hf b hb).trans (ih (by omega) (by omega))
  intro i hi
  have hupper := hanti 0 i (Nat.zero_le i) hi
  have hlower := hanti i (2 * t - 1) (by omega) (by omega)
  have hlo := hlow 0 (by omega)
  have hba := hbase 0 (by omega)
  obtain ⟨h₁, h₂⟩ := hflag i hi
  dsimp [f] at hupper hlower
  omega

/-- With odd meld size, uniform residue counts cannot saturate the draw-pair bound
once residue one has two draw pairs. -/
theorem FullWait.not_uniform_residues_at_odd_pair_bound {h : Multiset ℕ} {q s : ℕ}
    (hw : FullWait k (1 + k * q) ranks h) (hk : 4 ≤ k) (hodd : k % 2 = 1)
    (hq : 0 < q) (hs : s < k) (hpairs : k + 2 ≤ 2 * s) (hranks : k + 2 * s ≤ ranks) :
    ¬ ∀ r : Fin k, residueSize k h r = k * q + s := by
  intro huniform
  have hkpos : 0 < k := by omega
  let pairs := Finset.range (2 * s)
  have hmem (i : ℕ) : i ∈ pairs ↔ i < 2 * s := Finset.mem_range
  obtain ⟨anchor, low, base, hanchor, hflag, hlow, hbase, hpair⟩ :=
    hw.exists_drawPair_high_counts hk (by omega) rfl hq hs pairs
      (fun i hi => by have := (hmem i).mp hi; omega)
      (fun i _ => by rw [huniform]; omega)
  have hnext (i : ℕ) : i % k ≠ (i + 1) % k := by
    have hmod := Nat.mod_lt i hkpos
    rw [Nat.add_mod i 1 k, Nat.mod_eq_of_lt (show 1 < k by omega)]
    by_cases h : i % k + 1 < k
    · rw [Nat.mod_eq_of_lt h]
      omega
    · have heq : i % k + 1 = k := by omega
      rw [heq, Nat.mod_self]
      omega
  have hcounts := tight_pair_counts low base
    (fun i hi => hlow i ((hmem i).mpr hi))
    (fun i hi => hbase i ((hmem i).mpr hi))
    (fun i hi => by
      rw [hflag i ((hmem i).mpr hi)]
      split <;> omega)
    (fun i hi => hpair ((hmem i).mpr (by omega)) ((hmem (i + 1)).mpr hi)
      (by omega) (hnext i))
  have hfirst : 1 ∈ pairs := (hmem 1).mpr (by omega)
  have hsecond : k + 1 ∈ pairs := (hmem (k + 1)).mpr (by omega)
  have hres : (k + 1) % k = 1 % k := by simp
  obtain ⟨hanchor₁, hc₁⟩ := hanchor 1 hfirst
  obtain ⟨hanchor₂, hc₂⟩ := hanchor (k + 1) hsecond
  have heye : anchor 1 = anchor (k + 1) := by
    by_contra hne
    have htiles := count_add_count_le_residueSize h (rankResidue hkpos 1)
      hanchor₁ (hanchor₂.trans hres) hne
    rw [huniform] at htiles
    have hqk := Nat.le_mul_of_pos_right k hq
    omega
  obtain ⟨hb₁, hl₁⟩ := hcounts 1 (by omega)
  obtain ⟨hb₂, hl₂⟩ := hcounts (k + 1) (by omega)
  have hbelow : ¬ 1 + k ≤ anchor 1 := by
    intro h
    have hf := hflag 1 hfirst
    rw [ite_eq_left h] at hf
    omega
  have habove : k + 1 + k ≤ anchor (k + 1) := by
    by_contra h
    have hf := hflag (k + 1) hsecond
    rw [ite_eq_right h] at hf
    omega
  omega

/-- Counting both blocks of draw pairs gives a bound that remains sharp
through `3k` ranks for even meld sizes. -/
theorem FullWait.meld_count_lower_with_draw_pairs {h : Multiset ℕ} {q m : ℕ}
    (hw : FullWait k (1 + k * q) ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks) (hq : 0 < q)
    (hcard : h.card + 1 = (1 + k * q) + k * m) :
    q * (k - 1) + (min (ranks - k) (2 * k) + 1) / 2 ≤ m := by
  let L := min (ranks - k) (2 * k)
  change q * (k - 1) + (L + 1) / 2 ≤ m
  by_contra! hfail
  have hkpos : 0 < k := by omega
  have hL : L ≤ 2 * k := min_le_right _ _
  have hLr : L ≤ ranks - k := min_le_left _ _
  let s := m - q * (k - 1)
  have hcap := hw.meld_count_lower hk hkr hcard
  have hm : m = q * (k - 1) + s := by dsimp [s]; omega
  have hs : 2 * s < L := by omega
  rw [hm] at hcard
  obtain ⟨excess, t, hadd, htotal, ht, hmod⟩ := hw.exists_residue_excesses hk hkr hcard
  let pairs := (Finset.range L).filter (fun a => excess (rankResidue hkpos a) = t)
  obtain ⟨hts, hbudget⟩ := card_filter_le_of_drawPair_excess hkpos hL excess hmod htotal
  change L ≤ pairs.card + 2 * (s - t) at hbudget
  have hbound (a : ℕ) (ha : a ∈ pairs) : a < L :=
    Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hdraws (a : ℕ) (ha : a ∈ pairs) : a + k < ranks := by
    have := hbound a ha
    omega
  have hsize (a : ℕ) (ha : a ∈ pairs) :
      residueSize k h (rankResidue hkpos a) = 1 + k * q - 1 + t := by
    have he := (Finset.mem_filter.mp ha).2
    rw [← hadd, he]
    omega
  obtain ⟨_, low, base, _, _, hlow, hbase, hpair⟩ :=
    hw.exists_drawPair_high_counts hk hkr rfl hq ht pairs hdraws hsize
  have hpos : 0 < t := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < pairs.card by omega)
    exact (Nat.zero_le _).trans_lt (hlow a ha)
  have hclosed {a b : ℕ} (ha : a ∈ pairs) (hb : b < L) (he : a % k = b % k) : b ∈ pairs :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, by
      rw [← (Fin.ext he : rankResidue hkpos a = rankResidue hkpos b)]
      exact (Finset.mem_filter.mp ha).2⟩
  have hcount := card_le_twice_of_drawPair_counts hkpos hpos hL pairs hbound hclosed
    low base hlow hbase hpair
  omega

/-- For even meld sizes, the periodic construction attains the minimum
through `3k` ranks. -/
theorem minimum_meld_count_even_of_le_thrice {q : ℕ} (hk : 4 ≤ k) (hq : 0 < q)
    (heven : k % 2 = 0) (hkr : k ≤ ranks) (hranks : ranks ≤ 3 * k) :
    let minimum := q * (k - 1) + (ranks - k + 1) / 2
    (∃ h : Multiset ℕ, FullWait k (1 + k * q) ranks h ∧
      h.card + 1 = (1 + k * q) + k * minimum) ∧
    ∀ (h : Multiset ℕ) (m : ℕ), FullWait k (1 + k * q) ranks h →
      h.card + 1 = (1 + k * q) + k * m → minimum ≤ m := by
  dsimp only
  constructor
  · simpa only [periodicMeldCount_even k q ranks heven] using
      exists_fullWait_periodic q (by omega) hkr
  · intro h m hw hcard
    have hmin : min (ranks - k) (2 * k) = ranks - k := min_eq_left (by omega)
    simpa only [hmin] using hw.meld_count_lower_with_draw_pairs hk hkr hq hcard

/-- Each pair of repeated residue classes requires one meld above the capacity bound.
A remaining unpaired class requires one more. -/
theorem FullWait.meld_count_lower_with_repeated_residues {h : Multiset ℕ} {q m : ℕ}
    (hw : FullWait k (1 + k * q) ranks h) (hk : 4 ≤ k) (hkr : k ≤ ranks)
    (hq : 0 < q) (hcard : h.card + 1 = (1 + k * q) + k * m) :
    q * (k - 1) + (min (ranks - k) k + 1) / 2 ≤ m := by
  have hmin : min (ranks - k) k ≤ min (ranks - k) (2 * k) :=
    le_min (min_le_left _ _) ((min_le_right (ranks - k) k).trans (by omega))
  have hbound := hw.meld_count_lower_with_draw_pairs hk hkr hq hcard
  omega

/-- For even `k`, the first rank beyond `2k` forces another meld. -/
theorem FullWait.meld_count_lower_even_beyond_twice {h : Multiset ℕ} {q m : ℕ}
    (hw : FullWait k (1 + k * q) ranks h) (hk : 4 ≤ k) (heven : k % 2 = 0)
    (hranks : 2 * k < ranks) (hq : 0 < q)
    (hcard : h.card + 1 = (1 + k * q) + k * m) :
    q * (k - 1) + k / 2 + 1 ≤ m := by
  have hhalf : (k + 1) / 2 = k / 2 := by omega
  have hmin : k + 1 ≤ min (ranks - k) (2 * k) := le_min (by omega) (by omega)
  calc
    _ = q * (k - 1) + (k + 1) / 2 + 1 := by rw [hhalf]
    _ ≤ q * (k - 1) + (min (ranks - k) (2 * k) + 1) / 2 := by omega
    _ ≤ m := hw.meld_count_lower_with_draw_pairs hk (by omega) hq hcard

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

/-- The exact minimum at `2k+1` ranks for both parities of the meld size. -/
theorem minimum_meld_count_one_past_twice {q : ℕ} (hk : 4 ≤ k) (hq : 0 < q) :
    let minimum := q * (k - 1) + (k + 2) / 2
    (∃ h : Multiset ℕ, FullWait k (1 + k * q) (2 * k + 1) h ∧
      h.card + 1 = (1 + k * q) + k * minimum) ∧
    ∀ (h : Multiset ℕ) (m : ℕ), FullWait k (1 + k * q) (2 * k + 1) h →
      h.card + 1 = (1 + k * q) + k * m → minimum ≤ m := by
  dsimp only
  by_cases heven : k % 2 = 0
  · have hhalf : (k + 2) / 2 = k / 2 + 1 := by omega
    simpa only [hhalf, Nat.add_assoc] using minimum_meld_count_even_beyond_twice
      (ranks := 2 * k + 1) hk hq heven (by omega) (by omega)
  · have hodd : k % 2 = 1 := by omega
    have hhalf : (k + 2) / 2 = (k + 1) / 2 := by omega
    rw [hhalf]
    constructor
    · exact exists_fullWait_odd_one_past_twice q (by omega) hodd
    · intro h m hw hcard
      have hmin : min (2 * k + 1 - k) k = k := min_eq_right (by omega)
      simpa only [hmin] using hw.meld_count_lower_with_repeated_residues
        hk (by omega) hq hcard

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
