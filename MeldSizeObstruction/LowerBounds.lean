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

/-- The periodic construction attains the minimum for three or four extra ranks. -/
theorem minimum_meld_count_three_or_four_extra {q extra : ℕ} (hk : 4 ≤ k) (hq : 0 < q)
    (hextra : 3 ≤ extra) (hupper : extra ≤ 4) :
    (∃ h : Multiset ℕ, FullWait k (1 + k * q) (k + extra) h ∧
      h.card + 1 = (1 + k * q) + k * (q * (k - 1) + 2)) ∧
    ∀ (h : Multiset ℕ) (m : ℕ), FullWait k (1 + k * q) (k + extra) h →
      h.card + 1 = (1 + k * q) + k * m → q * (k - 1) + 2 ≤ m := by
  have hcount : periodicMeldCount k q (k + extra) = q * (k - 1) + 2 := by
    by_cases hsmall : extra < k
    · simp only [periodicMeldCount, Nat.add_sub_cancel_left, Nat.div_eq_of_lt hsmall,
        Nat.mod_eq_of_lt hsmall, zero_mul, Nat.add_zero]
      omega
    · have hk_eq : k = 4 := by omega
      have hextra_eq : extra = 4 := by omega
      subst k
      subst extra
      simp [periodicMeldCount]
  constructor
  · simpa only [hcount] using
      exists_fullWait_periodic (k := k) (ranks := k + extra) q (by omega) (by omega)
  · intro h m hw hc
    exact hw.meld_count_lower_of_three_extra_ranks hk (by omega) hq hc

end MeldSizeObstruction
