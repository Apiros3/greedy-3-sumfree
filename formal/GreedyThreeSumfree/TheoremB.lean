import GreedyThreeSumfree.NextDiagonalBasic

namespace GreedyThreeSumfree
namespace NextDiagonal

/-- Prefix set for Theorem B: `P = {1,g,c} union [2g+1,3g+1]`. -/
def InPrefix (g z : Nat) : Prop :=
  z = 1 ∨ z = g ∨ z = c g ∨ InH g z

/-- Candidate set for Theorem B.  Blocks are indexed by positive `q`. -/
def Candidate (g z : Nat) : Prop :=
  InPrefix g z ∨ ∃ q : Nat, 1 <= q ∧ InBlock g q z

theorem M_pos {g : Nat} (_h : Params g) : 0 < M g := by
  unfold M
  omega

theorem g_lt_c {g : Nat} (h : Params g) : g < c g := by
  have hg := h.five_le_g
  unfold c
  omega

theorem H_hi_lt_c {g : Nat} (_h : Params g) : 3 * g + 1 < c g := by
  unfold c
  omega

theorem c_lt_M {g : Nat} (h : Params g) : c g < M g := by
  have hg := h.five_le_g
  unfold c M
  omega

theorem blockLo_ge_one {g : Nat} (h : Params g) : 1 <= blockLo g := by
  have hg := h.five_le_g
  unfold blockLo
  omega

theorem blockHi_lt_M {g : Nat} (h : Params g) : blockHi g < M g := by
  have hg := h.five_le_g
  unfold blockHi M
  omega

theorem blockLo_le_blockHi (g : Nat) : blockLo g <= blockHi g := by
  unfold blockLo blockHi
  omega

theorem prefix_lt_M {g z : Nat} (h : Params g) (hz : InPrefix g z) :
    z < M g := by
  unfold InPrefix InH InInterval at hz
  rcases hz with rfl | rfl | rfl | hzH
  · have hg := h.five_le_g
    unfold M
    omega
  · have hg := h.five_le_g
    unfold M
    omega
  · exact c_lt_M h
  · have hzu := hzH.2
    have hg := h.five_le_g
    unfold M
    omega

theorem prefix_mod_eq {g z : Nat} (h : Params g) (hz : InPrefix g z) :
    z % M g = z := by
  exact Nat.mod_eq_of_lt (prefix_lt_M h hz)

theorem prefix_le_c {g z : Nat} (h : Params g) (hz : InPrefix g z) :
    z <= c g := by
  unfold InPrefix InH InInterval at hz
  rcases hz with rfl | rfl | rfl | hzH
  · unfold c
    omega
  · unfold c
    omega
  · omega
  · have hzu := hzH.2
    unfold c
    omega

theorem M_le_positive_multiple (g q : Nat) (hq : 1 <= q) :
    M g <= q * M g := by
  have hmul : 1 * M g <= q * M g := Nat.mul_le_mul_right (M g) hq
  simpa using hmul

theorem positive_block_ge_M {g q z : Nat} (hq : 1 <= q)
    (hz : InBlock g q z) : M g <= z := by
  have hM : M g <= q * M g := M_le_positive_multiple g q hq
  have hqM_le_lo : q * M g <= q * M g + blockLo g := Nat.le_add_right _ _
  exact Nat.le_trans hM (Nat.le_trans hqM_le_lo hz.1)

theorem inBlock_of_residue_interval {g q r : Nat}
    (hr : InInterval (blockLo g) (blockHi g) r) :
    InBlock g q (q * M g + r) := by
  rcases hr with ⟨hrlo, hrhi⟩
  unfold InBlock InInterval
  constructor
  · exact Nat.add_le_add_left hrlo (q * M g)
  · exact Nat.add_le_add_left hrhi (q * M g)

theorem block_mod_interval {g q z : Nat} (h : Params g)
    (hz : InBlock g q z) : InInterval (blockLo g) (blockHi g) (z % M g) := by
  let r := z - q * M g
  have hqM_le_lo : q * M g <= q * M g + blockLo g := Nat.le_add_right _ _
  have hqM_z : q * M g <= z := Nat.le_trans hqM_le_lo hz.1
  have hrlo : blockLo g <= r := by
    dsimp [r]
    have hlo : blockLo g + q * M g <= z := by
      simpa [Nat.add_comm] using hz.1
    exact Nat.le_sub_of_add_le hlo
  have hrhi : r <= blockHi g := by
    dsimp [r]
    rw [Nat.sub_le_iff_le_add]
    simpa [Nat.add_comm] using hz.2
  have hrM : r < M g := by
    have hbM : blockHi g < M g := blockHi_lt_M h
    omega
  have hz_eq : q * M g + r = z := by
    dsimp [r]
    exact Nat.add_sub_of_le hqM_z
  have hmod : z % M g = r := by
    rw [← hz_eq]
    rw [Nat.mul_comm q (M g)]
    rw [Nat.mul_add_mod_self_left]
    exact Nat.mod_eq_of_lt hrM
  rw [hmod]
  exact ⟨hrlo, hrhi⟩

theorem candidate_one (g : Nat) : Candidate g 1 := by
  left
  unfold InPrefix
  exact Or.inl rfl

theorem candidate_g (g : Nat) : Candidate g g := by
  left
  unfold InPrefix
  exact Or.inr (Or.inl rfl)

theorem candidate_c (g : Nat) : Candidate g (c g) := by
  left
  unfold InPrefix
  exact Or.inr (Or.inr (Or.inl rfl))

theorem candidate_of_H {g z : Nat} (hz : InH g z) : Candidate g z := by
  left
  unfold InPrefix
  exact Or.inr (Or.inr (Or.inr hz))

theorem candidate_of_block {g q z : Nat}
    (hq : 1 <= q) (hz : InBlock g q z) : Candidate g z := by
  right
  exact ⟨q, hq, hz⟩

theorem prefix_lt_positive_block {g q p z : Nat} (h : Params g)
    (hq : 1 <= q) (hp : InPrefix g p) (hz : InBlock g q z) : p < z := by
  have hpM : p < M g := prefix_lt_M h hp
  have hMz : M g <= z := positive_block_ge_M hq hz
  omega

theorem candidate_ge_one {g z : Nat} (h : Params g)
    (hz : Candidate g z) : 1 <= z := by
  unfold Candidate at hz
  rcases hz with hp | hb
  · unfold InPrefix InH InInterval at hp
    rcases hp with rfl | rfl | rfl | hzH
    · omega
    · have hg := h.five_le_g
      omega
    · unfold c
      omega
    · have hzl := hzH.1
      omega
  · rcases hb with ⟨q, hq, hzblock⟩
    have hMz : M g <= z := positive_block_ge_M hq hzblock
    have hMpos : 1 <= M g := by
      have hM := M_pos h
      omega
    omega

theorem candidate_ne_one_ge_g {g z : Nat} (h : Params g)
    (hz : Candidate g z) (hz_ne_one : z ≠ 1) : g <= z := by
  unfold Candidate at hz
  rcases hz with hp | hb
  · unfold InPrefix InH InInterval at hp
    rcases hp with rfl | rfl | rfl | hzH
    · contradiction
    · omega
    · have hgc := g_lt_c h
      omega
    · have hzl := hzH.1
      omega
  · rcases hb with ⟨q, hq, hzblock⟩
    have hMz : M g <= z := positive_block_ge_M hq hzblock
    have hgM : g <= M g := by
      unfold M
      omega
    exact Nat.le_trans hgM hMz

theorem candidate_lt_g_eq_one {g z : Nat} (h : Params g)
    (hz : Candidate g z) (hzlt : z < g) : z = 1 := by
  unfold Candidate at hz
  rcases hz with hp | hb
  · unfold InPrefix InH InInterval at hp
    rcases hp with h1 | hg | hc | hzH
    · exact h1
    · omega
    · have hgc := g_lt_c h
      omega
    · have hzl := hzH.1
      omega
  · rcases hb with ⟨q, hq, hzblock⟩
    have hMz : M g <= z := positive_block_ge_M hq hzblock
    have hgM : g <= M g := by
      unfold M
      omega
    omega

theorem candidate_gt_g_ge_H_lo {g z : Nat} (h : Params g)
    (hz : Candidate g z) (hgt : g < z) : 2 * g + 1 <= z := by
  unfold Candidate at hz
  rcases hz with hp | hb
  · unfold InPrefix InH InInterval at hp
    rcases hp with rfl | rfl | rfl | hzH
    · omega
    · omega
    · unfold c
      omega
    · exact hzH.1
  · rcases hb with ⟨q, hq, hzblock⟩
    have hMz : M g <= z := positive_block_ge_M hq hzblock
    have hMlo : 2 * g + 1 <= M g := by
      have hg := h.five_le_g
      unfold M
      omega
    exact Nat.le_trans hMlo hMz

theorem candidate_gt_g_lt_c_inH {g z : Nat} (h : Params g)
    (hz : Candidate g z) (hgt : g < z) (hltc : z < c g) : InH g z := by
  unfold Candidate at hz
  rcases hz with hp | hb
  · unfold InPrefix InH InInterval at hp
    rcases hp with rfl | rfl | rfl | hzH
    · have hg := h.five_le_g
      omega
    · omega
    · omega
    · exact hzH
  · rcases hb with ⟨q, hq, hzblock⟩
    have hMz : M g <= z := positive_block_ge_M hq hzblock
    have hcM := c_lt_M h
    omega

theorem candidate_ordered_ge_seed_sum {g x y w : Nat} (h : Params g)
    (hx : Candidate g x) (hy : Candidate g y) (hw : Candidate g w)
    (hxy : x < y) (hyw : y < w) :
    1 + g + (2 * g + 1) <= x + y + w := by
  have hx1 : 1 <= x := candidate_ge_one h hx
  have hy_ne_one : y ≠ 1 := by omega
  have hyg : g <= y := candidate_ne_one_ge_g h hy hy_ne_one
  have hg_lt_w : g < w := by omega
  have hwlo : 2 * g + 1 <= w := candidate_gt_g_ge_H_lo h hw hg_lt_w
  omega

/-- The interval prefix after the seed is safe. -/
theorem prefix_safe {g z : Nat} (h : Params g)
    (hz : InInterval (2 * g + 2) (3 * g + 1) z) :
    ¬ TripleSumFrom (Candidate g) z := by
  intro htriple
  rcases htriple with ⟨x, y, w, hx, hy, hw, hxy, hyw, _hwz, hsum⟩
  have hlo : 1 + g + (2 * g + 1) <= x + y + w :=
    candidate_ordered_ge_seed_sum h hx hy hw hxy hyw
  have hhi : z < 1 + g + (2 * g + 1) := seedTriple_gt_prefix h hz
  omega

/-- The singleton `c = 4g+3` is safe from triples in the earlier prefix. -/
theorem singleton_safe {g : Nat} (h : Params g) :
    ¬ TripleSumFrom (Candidate g) (c g) := by
  intro htriple
  rcases htriple with ⟨x, y, w, hx, hy, hw, hxy, hyw, hwc, hsum⟩
  have hx1 : 1 <= x := candidate_ge_one h hx
  have hy_ne_one : y ≠ 1 := by omega
  have hyg : g <= y := candidate_ne_one_ge_g h hy hy_ne_one
  by_cases hy_eq_g : y = g
  · have hxone : x = 1 := candidate_lt_g_eq_one h hx (by omega)
    have hwH : InH g w := candidate_gt_g_lt_c_inH h hw (by omega) hwc
    have hwle : w <= 3 * g + 1 := hwH.2
    unfold c at hsum
    omega
  · have hgy : g < y := by omega
    have hyH : InH g y := candidate_gt_g_lt_c_inH h hy hgy (by omega)
    have hylo : 2 * g + 1 <= y := hyH.1
    have hwlo : 2 * g + 2 <= w := by omega
    unfold c at hsum
    omega

theorem candidate_mod_ge_one {g z : Nat} (h : Params g)
    (hz : Candidate g z) : 1 <= z % M g := by
  unfold Candidate at hz
  rcases hz with hp | hb
  · rw [prefix_mod_eq h hp]
    exact candidate_ge_one h (Or.inl hp)
  · rcases hb with ⟨q, _hq, hzblock⟩
    have hres := block_mod_interval h hzblock
    have hblo := blockLo_ge_one h
    exact Nat.le_trans hblo hres.1

theorem candidate_ne_one_mod_ge_g {g z : Nat} (h : Params g)
    (hz : Candidate g z) (hz_ne_one : z ≠ 1) : g <= z % M g := by
  unfold Candidate at hz
  rcases hz with hp | hb
  · rw [prefix_mod_eq h hp]
    exact candidate_ne_one_ge_g h (Or.inl hp) hz_ne_one
  · rcases hb with ⟨q, _hq, hzblock⟩
    have hres := block_mod_interval h hzblock
    have hblo : g <= blockLo g := by
      unfold blockLo
      omega
    exact Nat.le_trans hblo hres.1

theorem candidate_gt_g_mod_ge_blockLo {g z : Nat} (h : Params g)
    (hz : Candidate g z) (hg_lt_z : g < z) : blockLo g <= z % M g := by
  unfold Candidate at hz
  rcases hz with hp | hb
  · rw [prefix_mod_eq h hp]
    unfold InPrefix InH InInterval at hp
    rcases hp with rfl | rfl | rfl | hzH
    · have hg := h.five_le_g
      omega
    · omega
    · unfold c blockLo
      omega
    · have hzlo := hzH.1
      unfold blockLo
      omega
  · rcases hb with ⟨q, _hq, hzblock⟩
    exact (block_mod_interval h hzblock).1

theorem candidate_mod_le_c {g z : Nat} (h : Params g)
    (hz : Candidate g z) : z % M g <= c g := by
  unfold Candidate at hz
  rcases hz with hp | hb
  · rw [prefix_mod_eq h hp]
    exact prefix_le_c h hp
  · rcases hb with ⟨q, _hq, hzblock⟩
    have hres := block_mod_interval h hzblock
    have hhi : z % M g <= blockHi g := hres.2
    unfold blockHi c at *
    omega

theorem candidate_mod_gt_blockHi_cases {g z : Nat} (h : Params g)
    (hz : Candidate g z) (hgt : blockHi g < z % M g) :
    (z = 3 * g + 1 ∧ z % M g = 3 * g + 1) ∨
      (z = c g ∧ z % M g = c g) := by
  unfold Candidate at hz
  rcases hz with hp | hb
  · have hmod := prefix_mod_eq h hp
    rw [hmod] at hgt
    unfold InPrefix InH InInterval at hp
    rcases hp with rfl | rfl | rfl | hzH
    · unfold blockHi at hgt
      omega
    · unfold blockHi at hgt
      omega
    · right
      exact ⟨rfl, hmod⟩
    · left
      have hzu := hzH.2
      unfold blockHi at hgt
      omega
  · rcases hb with ⟨q, _hq, hzblock⟩
    have hres := block_mod_interval h hzblock
    have hres_hi : z % M g <= blockHi g := hres.2
    omega

theorem candidate_two_high_residue_sum_le {g u v : Nat} (h : Params g)
    (hu : Candidate g u) (hv : Candidate g v) (huv : u < v)
    (huhigh : blockHi g < u % M g) (hvhigh : blockHi g < v % M g) :
    u % M g + v % M g <= (3 * g + 1) + c g := by
  have hucases := candidate_mod_gt_blockHi_cases h hu huhigh
  have hvcases := candidate_mod_gt_blockHi_cases h hv hvhigh
  rcases hucases with hucases | hucases <;>
    rcases hvcases with hvcases | hvcases <;>
    omega

theorem candidate_ordered_residue_sum_lower {g x y w : Nat} (h : Params g)
    (hx : Candidate g x) (hy : Candidate g y) (hw : Candidate g w)
    (hxy : x < y) (hyw : y < w) :
    3 * g + 1 <= x % M g + y % M g + w % M g := by
  have hx1 : 1 <= x % M g := candidate_mod_ge_one h hx
  have hx_pos : 1 <= x := candidate_ge_one h hx
  have hy_ne_one : y ≠ 1 := by omega
  have hyg : g <= y % M g := candidate_ne_one_mod_ge_g h hy hy_ne_one
  have hy_ge_g : g <= y := candidate_ne_one_ge_g h hy hy_ne_one
  have hg_lt_w : g < w := by omega
  have hwlo : blockLo g <= w % M g := candidate_gt_g_mod_ge_blockLo h hw hg_lt_w
  unfold blockLo at hwlo
  omega

theorem candidate_ordered_residue_sum_upper {g x y w : Nat} (h : Params g)
    (hx : Candidate g x) (hy : Candidate g y) (hw : Candidate g w)
    (hxy : x < y) (hyw : y < w) :
    x % M g + y % M g + w % M g <= c g + (3 * g + 1) + 3 * g := by
  have hxle : x % M g <= c g := candidate_mod_le_c h hx
  have hyle : y % M g <= c g := candidate_mod_le_c h hy
  have hwle : w % M g <= c g := candidate_mod_le_c h hw
  by_cases hxhigh : blockHi g < x % M g
  · by_cases hyhigh : blockHi g < y % M g
    · by_cases hwhigh : blockHi g < w % M g
      · have hxcases := candidate_mod_gt_blockHi_cases h hx hxhigh
        have hycases := candidate_mod_gt_blockHi_cases h hy hyhigh
        have hwcases := candidate_mod_gt_blockHi_cases h hw hwhigh
        rcases hxcases with hxcases | hxcases <;>
          rcases hycases with hycases | hycases <;>
          rcases hwcases with hwcases | hwcases <;>
          omega
      · have hpair := candidate_two_high_residue_sum_le h hx hy hxy hxhigh hyhigh
        unfold blockHi at hwhigh
        omega
    · by_cases hwhigh : blockHi g < w % M g
      · have hpair := candidate_two_high_residue_sum_le h hx hw (by omega) hxhigh hwhigh
        unfold blockHi at hyhigh
        omega
      · unfold blockHi at hyhigh hwhigh
        omega
  · by_cases hyhigh : blockHi g < y % M g
    · by_cases hwhigh : blockHi g < w % M g
      · have hpair := candidate_two_high_residue_sum_le h hy hw hyw hyhigh hwhigh
        unfold blockHi at hxhigh
        omega
      · unfold blockHi at hxhigh hwhigh
        omega
    · by_cases hwhigh : blockHi g < w % M g
      · unfold blockHi at hxhigh hyhigh
        omega
      · unfold blockHi at hxhigh hyhigh hwhigh
        omega

/--
Periodic block safety for Theorem B: a candidate in any positive block cannot
be a sum of three distinct smaller candidates.
-/
theorem periodic_block_safe {g q z : Nat} (h : Params g)
    (_hq : 1 <= q) (hz : InBlock g q z) :
    ¬ TripleSumFrom (Candidate g) z := by
  intro htriple
  rcases htriple with ⟨x, y, w, hx, hy, hw, hxy, hyw, _hwz, hsum⟩
  let s := x % M g + y % M g + w % M g
  let r := z % M g
  have hmod : s % M g = r := by
    dsimp [s, r]
    exact triple_sum_mod hsum
  have hzres := block_mod_interval h hz
  have hrlo : blockLo g <= r := by
    dsimp [r]
    exact hzres.1
  have hrhi : r <= blockHi g := by
    dsimp [r]
    exact hzres.2
  have hslo : 3 * g + 1 <= s := by
    dsimp [s]
    exact candidate_ordered_residue_sum_lower h hx hy hw hxy hyw
  have hshi : s <= c g + (3 * g + 1) + 3 * g := by
    dsimp [s]
    exact candidate_ordered_residue_sum_upper h hx hy hw hxy hyw
  have hr_lt_s : r < s := by
    unfold blockHi at hrhi
    omega
  have hdiff : s - r < M g := by
    unfold blockLo c M at *
    omega
  exact mod_eq_forbidden_between hmod hr_lt_s hdiff

theorem H_pair_sum_distinct {g t : Nat} (h : Params g)
    (ht : InInterval (4 * g + 3) (6 * g + 1) t) :
    ∃ u v : Nat, InH g u ∧ InH g v ∧ u < v ∧ u + v = t := by
  have hg := h.five_le_g
  have htlo := ht.1
  have hthi := ht.2
  have hLU : 2 * g + 1 < 3 * g + 1 := by
    omega
  have htNat :
      NatInterval (2 * (2 * g + 1) + 1) (2 * (3 * g + 1) - 1) t := by
    unfold NatInterval
    constructor <;> omega
  rcases interval_pair_sum_distinct hLU htNat with ⟨u, v, hu, hv, huv, hsum⟩
  refine ⟨u, v, ?_, ?_, huv, hsum⟩
  · simpa [InH, InInterval, NatInterval] using hu
  · simpa [InH, InInterval, NatInterval] using hv

theorem H_triple_sum_distinct {g t : Nat} (h : Params g)
    (ht : InInterval (6 * g + 6) (9 * g) t) :
    ∃ u v w : Nat,
      InH g u ∧ InH g v ∧ InH g w ∧ u < v ∧ v < w ∧ u + v + w = t := by
  have hg := h.five_le_g
  have htlo := ht.1
  have hthi := ht.2
  have hwidth : 2 * g + 1 + 2 <= 3 * g + 1 := by
    omega
  have htNat :
      NatInterval (3 * (2 * g + 1) + 3) (3 * (3 * g + 1) - 3) t := by
    unfold NatInterval
    constructor <;> omega
  rcases interval_triple_sum_distinct hwidth htNat with
    ⟨u, v, w, hu, hv, hw, huv, hvw, hsum⟩
  refine ⟨u, v, w, ?_, ?_, ?_, huv, hvw, hsum⟩
  · simpa [InH, InInterval, NatInterval] using hu
  · simpa [InH, InInterval, NatInterval] using hv
  · simpa [InH, InInterval, NatInterval] using hw

/-- Coverage of the first prefix gap `[3g+2,4g+2]` by `1 + g + H`. -/
theorem prefix_gap_cover_first {g z : Nat} (h : Params g)
    (hz : InInterval (3 * g + 2) (4 * g + 2) z) :
    TripleSumFrom (Candidate g) z := by
  let w := z - (1 + g)
  have hzl := hz.1
  have hzu := hz.2
  have hwlo : 2 * g + 1 <= w := by
    dsimp [w]
    apply Nat.le_sub_of_add_le
    omega
  have hwhi : w <= 3 * g + 1 := by
    dsimp [w]
    rw [Nat.sub_le_iff_le_add]
    omega
  have hwH : InH g w := by
    unfold InH InInterval
    exact ⟨hwlo, hwhi⟩
  have hsum : 1 + g + w = z := by
    dsimp [w]
    have hle : 1 + g <= z := by
      omega
    exact Nat.add_sub_of_le hle
  refine
    ⟨1, g, w, candidate_one g, candidate_g g, candidate_of_H hwH,
      ?_, ?_, ?_, hsum⟩
  · have hg := h.five_le_g
    omega
  · omega
  · omega

/-- Coverage of the second prefix gap from `1 + (H + H)_distinct`. -/
theorem prefix_second_gap_cover_one {g z : Nat} (h : Params g)
    (hz : InInterval (4 * g + 4) (6 * g + 2) z) :
    TripleSumFrom (Candidate g) z := by
  let t := z - 1
  have hzl := hz.1
  have hzu := hz.2
  have ht : InInterval (4 * g + 3) (6 * g + 1) t := by
    dsimp [t]
    constructor
    · apply Nat.le_sub_of_add_le
      omega
    · rw [Nat.sub_le_iff_le_add]
      omega
  rcases H_pair_sum_distinct h ht with ⟨u, v, hu, hv, huv, hsumuv⟩
  have hsum : 1 + u + v = z := by
    dsimp [t] at hsumuv
    omega
  refine
    ⟨1, u, v, candidate_one g, candidate_of_H hu, candidate_of_H hv,
      ?_, huv, ?_, hsum⟩
  · have hg := h.five_le_g
    have hulo := hu.1
    omega
  · omega

/-- Coverage of the second prefix gap from `g + (H + H)_distinct`. -/
theorem prefix_second_gap_cover_two {g z : Nat} (h : Params g)
    (hz : InInterval (5 * g + 3) (7 * g + 1) z) :
    TripleSumFrom (Candidate g) z := by
  let t := z - g
  have hzl := hz.1
  have hzu := hz.2
  have ht : InInterval (4 * g + 3) (6 * g + 1) t := by
    dsimp [t]
    constructor
    · apply Nat.le_sub_of_add_le
      omega
    · rw [Nat.sub_le_iff_le_add]
      omega
  rcases H_pair_sum_distinct h ht with ⟨u, v, hu, hv, huv, hsumuv⟩
  have hsum : g + u + v = z := by
    dsimp [t] at hsumuv
    omega
  refine
    ⟨g, u, v, candidate_g g, candidate_of_H hu, candidate_of_H hv,
      ?_, huv, ?_, hsum⟩
  · have hulo := hu.1
    omega
  · omega

/-- Coverage of the second prefix gap from `(H + H + H)_distinct`. -/
theorem prefix_second_gap_cover_three {g z : Nat} (h : Params g)
    (hz : InInterval (6 * g + 6) (9 * g) z) :
    TripleSumFrom (Candidate g) z := by
  rcases H_triple_sum_distinct h hz with
    ⟨u, v, w, hu, hv, hw, huv, hvw, hsum⟩
  refine
    ⟨u, v, w, candidate_of_H hu, candidate_of_H hv, candidate_of_H hw,
      huv, hvw, ?_, hsum⟩
  have hg := h.five_le_g
  have hulo := hu.1
  have hvlo := hv.1
  omega

/-- Coverage of the second prefix gap from `c + (H + H)_distinct`. -/
theorem prefix_second_gap_cover_four {g z : Nat} (h : Params g)
    (hz : InInterval (8 * g + 6) (10 * g + 4) z) :
    TripleSumFrom (Candidate g) z := by
  let t := z - c g
  have hzl := hz.1
  have hzu := hz.2
  have ht : InInterval (4 * g + 3) (6 * g + 1) t := by
    dsimp [t]
    constructor
    · apply Nat.le_sub_of_add_le
      unfold c
      omega
    · rw [Nat.sub_le_iff_le_add]
      unfold c
      omega
  rcases H_pair_sum_distinct h ht with ⟨u, v, hu, hv, huv, hsumuv⟩
  have hsum : u + v + c g = z := by
    dsimp [t] at hsumuv
    omega
  refine
    ⟨u, v, c g, candidate_of_H hu, candidate_of_H hv, candidate_c g,
      huv, ?_, ?_, hsum⟩
  · have hvhi := hv.2
    unfold c
    omega
  · have hg := h.five_le_g
    have hulo := hu.1
    omega

/-- Coverage of the second prefix gap `[4g+4,10g+4]`. -/
theorem prefix_second_gap_covered {g z : Nat} (h : Params g)
    (hz : InInterval (4 * g + 4) (10 * g + 4) z) :
    TripleSumFrom (Candidate g) z := by
  have hzl := hz.1
  have hzu := hz.2
  by_cases h1 : z <= 6 * g + 2
  · exact prefix_second_gap_cover_one h ⟨hzl, h1⟩
  · by_cases h2 : z <= 7 * g + 1
    · have hlo2 : 5 * g + 3 <= z := by
        omega
      exact prefix_second_gap_cover_two h ⟨hlo2, h2⟩
    · by_cases h3 : z <= 9 * g
      · have hlo3 : 6 * g + 6 <= z := by
          have hg := h.five_le_g
          omega
        exact prefix_second_gap_cover_three h ⟨hlo3, h3⟩
      · have hlo4 : 8 * g + 6 <= z := by
          have hg := h.five_le_g
          omega
        exact prefix_second_gap_cover_four h ⟨hlo4, hzu⟩

/-- Coverage of both prefix gaps before the first periodic block. -/
theorem prefix_gap_covered {g z : Nat} (h : Params g)
    (hz : InInterval (3 * g + 2) (4 * g + 2) z ∨
      InInterval (4 * g + 4) (10 * g + 4) z) :
    TripleSumFrom (Candidate g) z := by
  rcases hz with hzfirst | hzsecond
  · exact prefix_gap_cover_first h hzfirst
  · exact prefix_second_gap_covered h hzsecond

/-- Periodic-gap coverage from `1 + g + B_q`. -/
theorem periodic_gap_cover_one {g q z : Nat} (h : Params g)
    (hq : 1 <= q)
    (hz : InInterval (q * M g + (3 * g + 1))
      (q * M g + (4 * g + 1)) z) :
    TripleSumFrom (Candidate g) z := by
  let w := z - (1 + g)
  have hzl := hz.1
  have hzu := hz.2
  have hwlo : q * M g + blockLo g <= w := by
    dsimp [w]
    apply Nat.le_sub_of_add_le
    unfold blockLo
    omega
  have hwhi : w <= q * M g + blockHi g := by
    dsimp [w]
    rw [Nat.sub_le_iff_le_add]
    unfold blockHi
    omega
  have hwB : InBlock g q w := ⟨hwlo, hwhi⟩
  have hsum : 1 + g + w = z := by
    dsimp [w]
    have hle : 1 + g <= z := by
      omega
    exact Nat.add_sub_of_le hle
  refine
    ⟨1, g, w, candidate_one g, candidate_g g, candidate_of_block hq hwB,
      ?_, ?_, ?_, hsum⟩
  · have hg := h.five_le_g
    omega
  · exact prefix_lt_positive_block h hq (Or.inr (Or.inl rfl)) hwB
  · omega

/-- Periodic-gap coverage from `1 + H + B_q`. -/
theorem periodic_gap_cover_two {g q z : Nat} (h : Params g)
    (hq : 1 <= q)
    (hz : InInterval (q * M g + (4 * g + 2))
      (q * M g + (6 * g + 2)) z) :
    TripleSumFrom (Candidate g) z := by
  let T := z - (q * M g + 1)
  have hzl := hz.1
  have hzu := hz.2
  have hT_eq : q * M g + 1 + T = z := by
    dsimp [T]
    have hle : q * M g + 1 <= z := by
      omega
    exact Nat.add_sub_of_le hle
  have hTlo : blockLo g + (2 * g + 1) <= T := by
    dsimp [T]
    apply Nat.le_sub_of_add_le
    unfold blockLo
    omega
  have hThi : T <= blockHi g + (3 * g + 1) := by
    dsimp [T]
    rw [Nat.sub_le_iff_le_add]
    unfold blockHi
    omega
  by_cases hlow : T <= blockHi g + (2 * g + 1)
  · let u := 2 * g + 1
    let r := T - u
    let w := q * M g + r
    have hrlo : blockLo g <= r := by
      dsimp [r, u]
      apply Nat.le_sub_of_add_le
      exact hTlo
    have hrhi : r <= blockHi g := by
      dsimp [r, u]
      rw [Nat.sub_le_iff_le_add]
      exact hlow
    have huH : InH g u := by
      dsimp [u]
      unfold InH InInterval
      constructor <;> omega
    have hwB : InBlock g q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨hrlo, hrhi⟩
    have hsumr : u + r = T := by
      dsimp [r]
      have huT : u <= T := by
        have hblo := blockLo_ge_one h
        omega
      exact Nat.add_sub_of_le huT
    have hsum : 1 + u + w = z := by
      dsimp [w]
      omega
    refine
      ⟨1, u, w, candidate_one g, candidate_of_H huH,
        candidate_of_block hq hwB, ?_, ?_, ?_, hsum⟩
    · dsimp [u]
      have hg := h.five_le_g
      omega
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr (Or.inr huH))) hwB
    · omega
  · let u := T - blockHi g
    let w := q * M g + blockHi g
    have hbT : blockHi g <= T := by
      have hblo := blockLo_ge_one h
      omega
    have hulo : 2 * g + 1 <= u := by
      dsimp [u]
      apply Nat.le_sub_of_add_le
      omega
    have huhi : u <= 3 * g + 1 := by
      dsimp [u]
      rw [Nat.sub_le_iff_le_add]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hThi
    have huH : InH g u := by
      unfold InH InInterval
      exact ⟨hulo, huhi⟩
    have hwB : InBlock g q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨blockLo_le_blockHi g, Nat.le_refl _⟩
    have hsumb : blockHi g + u = T := by
      dsimp [u]
      exact Nat.add_sub_of_le hbT
    have hsum : 1 + u + w = z := by
      dsimp [w]
      omega
    refine
      ⟨1, u, w, candidate_one g, candidate_of_H huH,
        candidate_of_block hq hwB, ?_, ?_, ?_, hsum⟩
    · have hg := h.five_le_g
      omega
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr (Or.inr huH))) hwB
    · omega

/-- Periodic-gap coverage from `(H + H)_distinct + B_q`. -/
theorem periodic_gap_cover_three {g q z : Nat} (h : Params g)
    (hq : 1 <= q)
    (hz : InInterval (q * M g + (6 * g + 3))
      (q * M g + (9 * g + 1)) z) :
    TripleSumFrom (Candidate g) z := by
  let T := z - q * M g
  have hzl := hz.1
  have hzu := hz.2
  have hT_eq : q * M g + T = z := by
    dsimp [T]
    have hle : q * M g <= z := by
      omega
    exact Nat.add_sub_of_le hle
  have hTlo : blockLo g + (4 * g + 3) <= T := by
    dsimp [T]
    apply Nat.le_sub_of_add_le
    unfold blockLo
    omega
  have hThi : T <= blockHi g + (6 * g + 1) := by
    dsimp [T]
    rw [Nat.sub_le_iff_le_add]
    unfold blockHi
    omega
  by_cases hlow : T <= blockHi g + (4 * g + 3)
  · let u := 2 * g + 1
    let v := 2 * g + 2
    let r := T - (4 * g + 3)
    let w := q * M g + r
    have hrlo : blockLo g <= r := by
      dsimp [r]
      apply Nat.le_sub_of_add_le
      exact hTlo
    have hrhi : r <= blockHi g := by
      dsimp [r]
      rw [Nat.sub_le_iff_le_add]
      exact hlow
    have huH : InH g u := by
      dsimp [u]
      unfold InH InInterval
      constructor <;> omega
    have hvH : InH g v := by
      dsimp [v]
      unfold InH InInterval
      constructor
      · omega
      · have hg := h.five_le_g
        omega
    have hwB : InBlock g q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨hrlo, hrhi⟩
    have hpair : u + v = 4 * g + 3 := by
      dsimp [u, v]
      omega
    have hsumr : (4 * g + 3) + r = T := by
      dsimp [r]
      have hpT : 4 * g + 3 <= T := by
        have hblo := blockLo_ge_one h
        omega
      exact Nat.add_sub_of_le hpT
    have hsum : u + v + w = z := by
      dsimp [w]
      omega
    refine
      ⟨u, v, w, candidate_of_H huH, candidate_of_H hvH,
        candidate_of_block hq hwB, ?_, ?_, ?_, hsum⟩
    · dsimp [u, v]
      omega
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr (Or.inr hvH))) hwB
    · have hg := h.five_le_g
      omega
  · let p := T - blockHi g
    let w := q * M g + blockHi g
    have hbT : blockHi g <= T := by
      have hblo := blockLo_ge_one h
      omega
    have hplo : 4 * g + 3 <= p := by
      dsimp [p]
      apply Nat.le_sub_of_add_le
      omega
    have hphi : p <= 6 * g + 1 := by
      dsimp [p]
      rw [Nat.sub_le_iff_le_add]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hThi
    rcases H_pair_sum_distinct h ⟨hplo, hphi⟩ with
      ⟨u, v, huH, hvH, huv, hsumuv⟩
    have hwB : InBlock g q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨blockLo_le_blockHi g, Nat.le_refl _⟩
    have hsumb : blockHi g + p = T := by
      dsimp [p]
      exact Nat.add_sub_of_le hbT
    have hsum : u + v + w = z := by
      dsimp [w]
      omega
    refine
      ⟨u, v, w, candidate_of_H huH, candidate_of_H hvH,
        candidate_of_block hq hwB, huv, ?_, ?_, hsum⟩
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr (Or.inr hvH))) hwB
    · have hg := h.five_le_g
      omega

/-- Periodic-gap coverage from `c + H + B_q`. -/
theorem periodic_gap_cover_four {g q z : Nat} (h : Params g)
    (hq : 1 <= q)
    (hz : InInterval (q * M g + (8 * g + 4))
      (q * M g + (10 * g + 4)) z) :
    TripleSumFrom (Candidate g) z := by
  let T := z - (q * M g + c g)
  have hzl := hz.1
  have hzu := hz.2
  have hT_eq : q * M g + c g + T = z := by
    dsimp [T]
    have hle : q * M g + c g <= z := by
      unfold c
      omega
    exact Nat.add_sub_of_le hle
  have hTlo : blockLo g + (2 * g + 1) <= T := by
    dsimp [T]
    apply Nat.le_sub_of_add_le
    unfold c blockLo
    omega
  have hThi : T <= blockHi g + (3 * g + 1) := by
    dsimp [T]
    rw [Nat.sub_le_iff_le_add]
    unfold c blockHi
    omega
  by_cases hlow : T <= blockHi g + (2 * g + 1)
  · let u := 2 * g + 1
    let r := T - u
    let w := q * M g + r
    have hrlo : blockLo g <= r := by
      dsimp [r, u]
      apply Nat.le_sub_of_add_le
      exact hTlo
    have hrhi : r <= blockHi g := by
      dsimp [r, u]
      rw [Nat.sub_le_iff_le_add]
      exact hlow
    have huH : InH g u := by
      dsimp [u]
      unfold InH InInterval
      constructor <;> omega
    have hwB : InBlock g q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨hrlo, hrhi⟩
    have hsumr : u + r = T := by
      dsimp [r]
      have huT : u <= T := by
        have hblo := blockLo_ge_one h
        omega
      exact Nat.add_sub_of_le huT
    have hsum : u + c g + w = z := by
      dsimp [w]
      omega
    refine
      ⟨u, c g, w, candidate_of_H huH, candidate_c g,
        candidate_of_block hq hwB, ?_, ?_, ?_, hsum⟩
    · have huhi := huH.2
      unfold c
      omega
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr (Or.inl rfl))) hwB
    · have hg := h.five_le_g
      omega
  · let u := T - blockHi g
    let w := q * M g + blockHi g
    have hbT : blockHi g <= T := by
      have hblo := blockLo_ge_one h
      omega
    have hulo : 2 * g + 1 <= u := by
      dsimp [u]
      apply Nat.le_sub_of_add_le
      omega
    have huhi : u <= 3 * g + 1 := by
      dsimp [u]
      rw [Nat.sub_le_iff_le_add]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hThi
    have huH : InH g u := by
      unfold InH InInterval
      exact ⟨hulo, huhi⟩
    have hwB : InBlock g q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨blockLo_le_blockHi g, Nat.le_refl _⟩
    have hsumb : blockHi g + u = T := by
      dsimp [u]
      exact Nat.add_sub_of_le hbT
    have hsum : u + c g + w = z := by
      dsimp [w]
      omega
    refine
      ⟨u, c g, w, candidate_of_H huH, candidate_c g,
        candidate_of_block hq hwB, ?_, ?_, ?_, hsum⟩
    · have huhi' := huH.2
      unfold c
      omega
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr (Or.inl rfl))) hwB
    · have hg := h.five_le_g
      omega

/--
Full periodic-gap coverage: every value after `B_q` and before `B_{q+1}` is
covered by three distinct smaller candidates.
-/
theorem periodic_gap_covered {g q z : Nat} (h : Params g)
    (hq : 1 <= q)
    (hz : InInterval (q * M g + blockHi g + 1)
      ((q + 1) * M g + blockLo g - 1) z) :
    TripleSumFrom (Candidate g) z := by
  have hzl := hz.1
  have hzu := hz.2
  by_cases h1 : z <= q * M g + (4 * g + 1)
  · have hlo1 : q * M g + (3 * g + 1) <= z := by
      unfold blockHi at hzl
      omega
    exact periodic_gap_cover_one h hq ⟨hlo1, h1⟩
  · by_cases h2 : z <= q * M g + (6 * g + 2)
    · have hlo2 : q * M g + (4 * g + 2) <= z := by
        omega
      exact periodic_gap_cover_two h hq ⟨hlo2, h2⟩
    · by_cases h3 : z <= q * M g + (9 * g + 1)
      · have hlo3 : q * M g + (6 * g + 3) <= z := by
          omega
        exact periodic_gap_cover_three h hq ⟨hlo3, h3⟩
      · have hlo4 : q * M g + (8 * g + 4) <= z := by
          have hg := h.five_le_g
          omega
        have hhi4 : z <= q * M g + (10 * g + 4) := by
          have hupper :
              (q + 1) * M g + blockLo g - 1 = q * M g + (10 * g + 4) := by
            rw [Nat.add_mul, Nat.one_mul]
            unfold M blockLo
            omega
          omega
        exact periodic_gap_cover_four h hq ⟨hlo4, hhi4⟩

/-- Combined coverage for the two prefix gaps and all positive periodic gaps. -/
theorem candidate_gap_covered {g z : Nat} (h : Params g)
    (hz : (InInterval (3 * g + 2) (4 * g + 2) z ∨
        InInterval (4 * g + 4) (10 * g + 4) z) ∨
      ∃ q : Nat, 1 <= q ∧
        InInterval (q * M g + blockHi g + 1)
          ((q + 1) * M g + blockLo g - 1) z) :
    TripleSumFrom (Candidate g) z := by
  rcases hz with hzprefix | hzperiodic
  · exact prefix_gap_covered h hzprefix
  · rcases hzperiodic with ⟨q, hq, hzq⟩
    exact periodic_gap_covered h hq hzq

/--
Every omitted value above the seed threshold `2g+1` is in one of the covered
gaps.
-/
theorem omitted_gt_seed_covered {g z : Nat} (h : Params g)
    (hzgt : 2 * g + 1 < z) (hzomitted : ¬ Candidate g z) :
    TripleSumFrom (Candidate g) z := by
  have hnotPrefix : ¬ InPrefix g z := by
    intro hp
    exact hzomitted (Or.inl hp)
  have hz_after_H : 3 * g + 2 <= z := by
    by_cases hle : z <= 3 * g + 1
    · have hp : InPrefix g z := by
        unfold InPrefix
        exact Or.inr (Or.inr (Or.inr (by
          unfold InH InInterval
          constructor <;> omega)))
      exact False.elim (hnotPrefix hp)
    · omega
  by_cases hfirst : z <= 4 * g + 2
  · exact prefix_gap_cover_first h ⟨hz_after_H, hfirst⟩
  · by_cases hzc : z = c g
    · exact False.elim (hzomitted (by
        rw [hzc]
        exact candidate_c g))
    · have hz_after_c : 4 * g + 4 <= z := by
        unfold c at hzc
        omega
      by_cases hsecond : z <= 10 * g + 4
      · exact prefix_second_gap_covered h ⟨hz_after_c, hsecond⟩
      · let q := z / M g
        let r := z % M g
        have hMpos : 0 < M g := M_pos h
        have hz_ge_first : M g + blockLo g <= z := by
          unfold M blockLo
          omega
        have hqpos : 1 <= q := by
          dsimp [q]
          apply Nat.div_pos
          · have hblo := blockLo_ge_one h
            omega
          · exact hMpos
        have hrM : r < M g := by
          dsimp [r]
          exact Nat.mod_lt z hMpos
        have hz_eq : z = q * M g + r := by
          dsimp [q, r]
          simpa [Nat.mul_comm] using (Nat.div_add_mod z (M g)).symm
        by_cases hrlo : r < blockLo g
        · have hqtwo : 2 <= q := by
            by_cases hqone : q = 1
            · have hlt_first : z < M g + blockLo g := by
                rw [hz_eq, hqone]
                omega
              omega
            · omega
          have hqprev : 1 <= q - 1 := by
            omega
          have hzgap :
              InInterval ((q - 1) * M g + blockHi g + 1)
                (((q - 1) + 1) * M g + blockLo g - 1) z := by
            constructor
            · have hq_mul : q * M g = (q - 1) * M g + M g := by
                have hq_eq : (q - 1) + 1 = q := by
                  omega
                calc
                  q * M g = ((q - 1) + 1) * M g := by rw [hq_eq]
                  _ = (q - 1) * M g + 1 * M g := by rw [Nat.add_mul]
                  _ = (q - 1) * M g + M g := by rw [Nat.one_mul]
              rw [hz_eq, hq_mul]
              unfold M blockHi
              omega
            · rw [hz_eq]
              have hq_eq : (q - 1) + 1 = q := by
                omega
              rw [hq_eq]
              omega
          exact periodic_gap_covered h hqprev hzgap
        · have hrlo' : blockLo g <= r := by
            omega
          by_cases hrhi : r <= blockHi g
          · have hblock : InBlock g q z := by
              rw [hz_eq]
              exact inBlock_of_residue_interval ⟨hrlo', hrhi⟩
            exact False.elim (hzomitted (candidate_of_block hqpos hblock))
          · have hzgap :
                InInterval (q * M g + blockHi g + 1)
                  ((q + 1) * M g + blockLo g - 1) z := by
              constructor
              · rw [hz_eq]
                omega
              · rw [hz_eq, Nat.add_mul, Nat.one_mul]
                have hblo := blockLo_ge_one h
                omega
            exact periodic_gap_covered h hqpos hzgap

theorem candidate_gt_seed_safe {g z : Nat} (h : Params g)
    (hzgt : 2 * g + 1 < z) (hzcandidate : Candidate g z) :
    ¬ TripleSumFrom (Candidate g) z := by
  unfold Candidate at hzcandidate
  rcases hzcandidate with hp | hb
  · unfold InPrefix at hp
    rcases hp with rfl | rfl | rfl | hzH
    · omega
    · have hg := h.five_le_g
      omega
    · exact singleton_safe h
    · have hzprefix : InInterval (2 * g + 2) (3 * g + 1) z := by
        unfold InH InInterval at hzH
        constructor
        · omega
        · exact hzH.2
      exact prefix_safe h hzprefix
  · rcases hb with ⟨q, hq, hzblock⟩
    exact periodic_block_safe h hq hzblock

/--
Exact Theorem B characterization above the seed threshold: the candidates are
precisely the values not represented by a triple of distinct smaller
candidates.
-/
theorem exact_characterization {g z : Nat} (h : Params g)
    (hzgt : 2 * g + 1 < z) :
    Candidate g z ↔ ¬ TripleSumFrom (Candidate g) z := by
  constructor
  · intro hzcandidate
    exact candidate_gt_seed_safe h hzgt hzcandidate
  · intro hsafe
    by_cases hzcandidate : Candidate g z
    · exact hzcandidate
    · exact False.elim (hsafe (omitted_gt_seed_covered h hzgt hzcandidate))

end NextDiagonal
end GreedyThreeSumfree
