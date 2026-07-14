import Std
import GreedyThreeSumfree.SeededGreedy
import GreedyThreeSumfree.IntervalSumWitnesses

namespace GreedyThreeSumfree

/-- Standing hypotheses from the strengthened theorem: `g >= 3` and `2 <= d <= g`. -/
structure Params (g d : Nat) : Prop where
  d_ge_two : 2 <= d
  d_le_g : d <= g
  three_le_g : 3 <= g

/-- The eventual period modulus `M = 5g + 2d`. -/
def M (g d : Nat) : Nat := 5 * g + 2 * d

/-- The first residue in a periodic block. -/
def a (g d : Nat) : Nat := g + d - 2

/-- The last residue in a periodic block. -/
def b (g d : Nat) : Nat := 2 * g + d - 2

/-- Closed interval membership for natural numbers. -/
def InInterval (lo hi n : Nat) : Prop := lo <= n ∧ n <= hi

/-- Prefix set `P = {1,g} union [g+d,2g+d]`. -/
def InPrefix (g d z : Nat) : Prop :=
  z = 1 ∨ z = g ∨ InInterval (g + d) (2 * g + d) z

/-- Periodic block `B_q = [qM+a,qM+b]`. -/
def InBlock (g d q z : Nat) : Prop :=
  InInterval (q * M g d + a g d) (q * M g d + b g d) z

/-- Candidate set from Theorem A.  Blocks are indexed by positive `q`. -/
def CandidateA (g d z : Nat) : Prop :=
  InPrefix g d z ∨ ∃ q : Nat, 1 <= q ∧ InBlock g d q z

theorem add_three_mod (x y w m : Nat) :
    (x + y + w) % m = (x % m + y % m + w % m) % m := by
  simp [Nat.add_mod]

theorem triple_sum_mod {x y w z m : Nat} (hsum : x + y + w = z) :
    (x % m + y % m + w % m) % m = z % m := by
  rw [← hsum]
  symm
  exact add_three_mod x y w m

theorem mod_eq_forbidden_between {m s r : Nat}
    (hmod : s % m = r) (hr_lt : r < s) (hdiff : s - r < m) : False := by
  have hdvd : m ∣ s - r := by
    have h0 : m ∣ s - s % m := Nat.dvd_sub_mod s
    simpa [hmod] using h0
  have hpos : 0 < s - r := by omega
  have hle : m <= s - r := Nat.le_of_dvd hpos hdvd
  omega

theorem d_le_g {g d : Nat} (h : Params g d) : d <= g := by
  exact h.d_le_g

theorem three_le_g {g d : Nat} (h : Params g d) : 3 <= g := by
  exact h.three_le_g

theorem d_pos {g d : Nat} (h : Params g d) : 0 < d := by
  have hd := h.d_ge_two
  omega

theorem g_le_M (g d : Nat) : g <= M g d := by
  unfold M
  omega

theorem g_add_d_le_M (g d : Nat) : g + d <= M g d := by
  unfold M
  omega

theorem M_le_positive_multiple (g d q : Nat) (hq : 1 <= q) :
    M g d <= q * M g d := by
  have hmul : 1 * M g d <= q * M g d := Nat.mul_le_mul_right (M g d) hq
  simpa using hmul

theorem positive_block_ge_M {g d q z : Nat} (hq : 1 <= q)
    (hz : InBlock g d q z) : M g d <= z := by
  have hM : M g d <= q * M g d := M_le_positive_multiple g d q hq
  have hqM_le_lo : q * M g d <= q * M g d + a g d := Nat.le_add_right _ _
  exact Nat.le_trans hM (Nat.le_trans hqM_le_lo hz.1)

theorem candidateA_ge_one {g d z : Nat} (h : Params g d)
    (hz : CandidateA g d z) : 1 <= z := by
  unfold CandidateA at hz
  rcases hz with hp | hb
  · unfold InPrefix InInterval at hp
    rcases hp with rfl | rfl | hzint
    · omega
    · have hg := h.three_le_g
      omega
    · have hg := h.three_le_g
      have hd := h.d_ge_two
      omega
  · rcases hb with ⟨q, hq, hzblock⟩
    have hMz : M g d <= z := positive_block_ge_M hq hzblock
    have hMpos : 1 <= M g d := by
      have hg := h.three_le_g
      have hd := h.d_ge_two
      unfold M
      omega
    omega

theorem candidateA_ne_one_ge_g {g d z : Nat} (h : Params g d)
    (hz : CandidateA g d z) (hz_ne_one : z ≠ 1) : g <= z := by
  unfold CandidateA at hz
  rcases hz with hp | hb
  · unfold InPrefix InInterval at hp
    rcases hp with rfl | rfl | hzint
    · contradiction
    · omega
    · have hd := h.d_ge_two
      omega
  · rcases hb with ⟨q, hq, hzblock⟩
    have hMz : M g d <= z := positive_block_ge_M hq hzblock
    have hgM : g <= M g d := g_le_M g d
    exact Nat.le_trans hgM hMz

theorem candidateA_gt_g_ge_g_add_d {g d z : Nat} (h : Params g d)
    (hz : CandidateA g d z) (hg_lt_z : g < z) : g + d <= z := by
  unfold CandidateA at hz
  rcases hz with hp | hb
  · unfold InPrefix InInterval at hp
    rcases hp with rfl | rfl | hzint
    · have hg := h.three_le_g
      omega
    · omega
    · exact hzint.1
  · rcases hb with ⟨q, hq, hzblock⟩
    have hMz : M g d <= z := positive_block_ge_M hq hzblock
    have hgdM : g + d <= M g d := g_add_d_le_M g d
    exact Nat.le_trans hgdM hMz

theorem candidateA_triple_ge_seed_sum {g d x y w : Nat} (h : Params g d)
    (hx : CandidateA g d x) (hy : CandidateA g d y) (hw : CandidateA g d w)
    (hxy : x < y) (hyw : y < w) :
    1 + g + (g + d) <= x + y + w := by
  have hx1 : 1 <= x := candidateA_ge_one h hx
  have hy_ne_one : y ≠ 1 := by omega
  have hyg : g <= y := candidateA_ne_one_ge_g h hy hy_ne_one
  have hg_lt_w : g < w := by omega
  have hwgd : g + d <= w := candidateA_gt_g_ge_g_add_d h hw hg_lt_w
  omega

theorem candidateA_one (g d : Nat) : CandidateA g d 1 := by
  left
  unfold InPrefix
  exact Or.inl rfl

theorem candidateA_g (g d : Nat) : CandidateA g d g := by
  left
  unfold InPrefix
  exact Or.inr (Or.inl rfl)

theorem candidateA_of_H {g d z : Nat}
    (hz : InInterval (g + d) (2 * g + d) z) : CandidateA g d z := by
  left
  unfold InPrefix
  exact Or.inr (Or.inr hz)

theorem candidateA_of_block {g d q z : Nat}
    (hq : 1 <= q) (hz : InBlock g d q z) : CandidateA g d z := by
  right
  exact ⟨q, hq, hz⟩

theorem a_ge_one {g d : Nat} (h : Params g d) : 1 <= a g d := by
  have hg := h.three_le_g
  have hd := h.d_ge_two
  unfold a
  omega

theorem g_le_a {g d : Nat} (h : Params g d) : g <= a g d := by
  have hd := h.d_ge_two
  unfold a
  omega

/-- The residue interval `[a,b]` is nonempty under the theorem hypotheses. -/
theorem blockStart_le_blockEnd {g d : Nat} (h : Params g d) : a g d <= b g d := by
  have hd := h.d_ge_two
  unfold a b
  omega

theorem b_lt_M {g d : Nat} (h : Params g d) : b g d < M g d := by
  have hg := h.three_le_g
  have hd := h.d_ge_two
  unfold b M
  omega

theorem b_add_two_lt_M {g d : Nat} (h : Params g d) : b g d + 2 < M g d := by
  have hg := h.three_le_g
  have hd := h.d_ge_two
  unfold b M
  omega

theorem b_add_one_lt_M {g d : Nat} (h : Params g d) : b g d + 1 < M g d := by
  have hb2 := b_add_two_lt_M h
  omega

theorem prefix_le_b_add_two {g d z : Nat} (h : Params g d)
    (hz : InPrefix g d z) : z <= b g d + 2 := by
  unfold InPrefix InInterval at hz
  rcases hz with rfl | rfl | hzint
  · have hg := h.three_le_g
    have hd := h.d_ge_two
    unfold b
    omega
  · have hd := h.d_ge_two
    unfold b
    omega
  · have hzu := hzint.2
    unfold b
    omega

theorem prefix_lt_M {g d z : Nat} (h : Params g d)
    (hz : InPrefix g d z) : z < M g d := by
  have hle := prefix_le_b_add_two h hz
  have hlt := b_add_two_lt_M h
  omega

theorem prefix_mod_eq {g d z : Nat} (h : Params g d)
    (hz : InPrefix g d z) : z % M g d = z := by
  exact Nat.mod_eq_of_lt (prefix_lt_M h hz)

theorem prefix_lt_positive_block {g d q p z : Nat} (h : Params g d)
    (hq : 1 <= q) (hp : InPrefix g d p) (hz : InBlock g d q z) : p < z := by
  have hpM : p < M g d := prefix_lt_M h hp
  have hMz : M g d <= z := positive_block_ge_M hq hz
  omega

theorem inBlock_of_residue_interval {g d q r : Nat}
    (hr : InInterval (a g d) (b g d) r) : InBlock g d q (q * M g d + r) := by
  rcases hr with ⟨hrlo, hrhi⟩
  unfold InBlock InInterval
  constructor
  · exact Nat.add_le_add_left hrlo (q * M g d)
  · exact Nat.add_le_add_left hrhi (q * M g d)

theorem block_mod_interval {g d q z : Nat} (h : Params g d)
    (hz : InBlock g d q z) : InInterval (a g d) (b g d) (z % M g d) := by
  let r := z - q * M g d
  have hqM_le_lo : q * M g d <= q * M g d + a g d := Nat.le_add_right _ _
  have hqM_z : q * M g d <= z := Nat.le_trans hqM_le_lo hz.1
  have hrlo : a g d <= r := by
    dsimp [r]
    have hlo : a g d + q * M g d <= z := by
      simpa [Nat.add_comm] using hz.1
    exact Nat.le_sub_of_add_le hlo
  have hrhi : r <= b g d := by
    dsimp [r]
    rw [Nat.sub_le_iff_le_add]
    simpa [Nat.add_comm] using hz.2
  have hrM : r < M g d := by
    have hbM : b g d < M g d := b_lt_M h
    omega
  have hz_eq : q * M g d + r = z := by
    dsimp [r]
    exact Nat.add_sub_of_le hqM_z
  have hmod : z % M g d = r := by
    rw [← hz_eq]
    rw [Nat.mul_comm q (M g d)]
    rw [Nat.mul_add_mod_self_left]
    exact Nat.mod_eq_of_lt hrM
  rw [hmod]
  exact ⟨hrlo, hrhi⟩

theorem candidateA_mod_le_b_add_two {g d z : Nat} (h : Params g d)
    (hz : CandidateA g d z) : z % M g d <= b g d + 2 := by
  unfold CandidateA at hz
  rcases hz with hp | hb
  · rw [prefix_mod_eq h hp]
    exact prefix_le_b_add_two h hp
  · rcases hb with ⟨q, _hq, hzblock⟩
    have hres := block_mod_interval h hzblock
    have hres_hi : z % M g d <= b g d := hres.2
    omega

theorem candidateA_mod_ge_one {g d z : Nat} (h : Params g d)
    (hz : CandidateA g d z) : 1 <= z % M g d := by
  unfold CandidateA at hz
  rcases hz with hp | hb
  · rw [prefix_mod_eq h hp]
    exact candidateA_ge_one h (Or.inl hp)
  · rcases hb with ⟨q, _hq, hzblock⟩
    have hres := block_mod_interval h hzblock
    have hres_lo : a g d <= z % M g d := hres.1
    have ha := a_ge_one h
    omega

theorem candidateA_ne_one_mod_ge_g {g d z : Nat} (h : Params g d)
    (hz : CandidateA g d z) (hz_ne_one : z ≠ 1) : g <= z % M g d := by
  unfold CandidateA at hz
  rcases hz with hp | hb
  · rw [prefix_mod_eq h hp]
    exact candidateA_ne_one_ge_g h (Or.inl hp) hz_ne_one
  · rcases hb with ⟨q, _hq, hzblock⟩
    have hres := block_mod_interval h hzblock
    have hres_lo : a g d <= z % M g d := hres.1
    have hga := g_le_a h
    omega

theorem candidateA_gt_g_mod_ge_a {g d z : Nat} (h : Params g d)
    (hz : CandidateA g d z) (hg_lt_z : g < z) : a g d <= z % M g d := by
  unfold CandidateA at hz
  rcases hz with hp | hb
  · rw [prefix_mod_eq h hp]
    unfold InPrefix InInterval at hp
    rcases hp with rfl | rfl | hzint
    · have hg := h.three_le_g
      omega
    · omega
    · have hzlo := hzint.1
      unfold a
      omega
  · rcases hb with ⟨q, _hq, hzblock⟩
    exact (block_mod_interval h hzblock).1

theorem candidateA_mod_gt_b_value {g d z : Nat} (h : Params g d)
    (hz : CandidateA g d z) (hgt : b g d < z % M g d) :
    z = b g d + 1 ∨ z = b g d + 2 := by
  unfold CandidateA at hz
  rcases hz with hp | hb
  · have hmod := prefix_mod_eq h hp
    have hle := prefix_le_b_add_two h hp
    rw [hmod] at hgt
    omega
  · rcases hb with ⟨q, _hq, hzblock⟩
    have hres := block_mod_interval h hzblock
    have hres_hi : z % M g d <= b g d := hres.2
    omega

theorem candidateA_mod_gt_b_cases {g d z : Nat} (h : Params g d)
    (hz : CandidateA g d z) (hgt : b g d < z % M g d) :
    (z = b g d + 1 ∧ z % M g d = b g d + 1) ∨
      (z = b g d + 2 ∧ z % M g d = b g d + 2) := by
  have hval := candidateA_mod_gt_b_value h hz hgt
  rcases hval with hval | hval
  · left
    constructor
    · exact hval
    · rw [hval]
      exact Nat.mod_eq_of_lt (b_add_one_lt_M h)
  · right
    constructor
    · exact hval
    · rw [hval]
      exact Nat.mod_eq_of_lt (b_add_two_lt_M h)

theorem candidateA_two_high_residue_sum_le {g d u v : Nat} (h : Params g d)
    (hu : CandidateA g d u) (hv : CandidateA g d v) (huv : u < v)
    (huhigh : b g d < u % M g d) (hvhigh : b g d < v % M g d) :
    u % M g d + v % M g d <= (b g d + 1) + (b g d + 2) := by
  have hucases := candidateA_mod_gt_b_cases h hu huhigh
  have hvcases := candidateA_mod_gt_b_cases h hv hvhigh
  rcases hucases with hucases | hucases <;>
    rcases hvcases with hvcases | hvcases <;>
    omega

theorem candidateA_ordered_residue_sum_lower {g d x y w : Nat} (h : Params g d)
    (hx : CandidateA g d x) (hy : CandidateA g d y) (hw : CandidateA g d w)
    (hxy : x < y) (hyw : y < w) :
    1 + g + a g d <= x % M g d + y % M g d + w % M g d := by
  have hx1 : 1 <= x % M g d := candidateA_mod_ge_one h hx
  have hx_pos : 1 <= x := candidateA_ge_one h hx
  have hy_ne_one : y ≠ 1 := by omega
  have hyg : g <= y % M g d := candidateA_ne_one_mod_ge_g h hy hy_ne_one
  have hy_ge_g : g <= y := candidateA_ne_one_ge_g h hy hy_ne_one
  have hg_lt_w : g < w := by omega
  have hwa : a g d <= w % M g d := candidateA_gt_g_mod_ge_a h hw hg_lt_w
  omega

theorem candidateA_ordered_residue_sum_upper {g d x y w : Nat} (h : Params g d)
    (hx : CandidateA g d x) (hy : CandidateA g d y) (hw : CandidateA g d w)
    (hxy : x < y) (hyw : y < w) :
    x % M g d + y % M g d + w % M g d <=
      (b g d + 2) + (b g d + 1) + b g d := by
  have hxle : x % M g d <= b g d + 2 := candidateA_mod_le_b_add_two h hx
  have hyle : y % M g d <= b g d + 2 := candidateA_mod_le_b_add_two h hy
  have hwle : w % M g d <= b g d + 2 := candidateA_mod_le_b_add_two h hw
  by_cases hxhigh : b g d < x % M g d
  · by_cases hyhigh : b g d < y % M g d
    · by_cases hwhigh : b g d < w % M g d
      · have hxcases := candidateA_mod_gt_b_cases h hx hxhigh
        have hycases := candidateA_mod_gt_b_cases h hy hyhigh
        have hwcases := candidateA_mod_gt_b_cases h hw hwhigh
        rcases hxcases with hxcases | hxcases <;>
          rcases hycases with hycases | hycases <;>
          rcases hwcases with hwcases | hwcases <;>
          omega
      · have hpair := candidateA_two_high_residue_sum_le h hx hy hxy hxhigh hyhigh
        omega
    · by_cases hwhigh : b g d < w % M g d
      · have hpair := candidateA_two_high_residue_sum_le h hx hw (by omega) hxhigh hwhigh
        omega
      · omega
  · by_cases hyhigh : b g d < y % M g d
    · by_cases hwhigh : b g d < w % M g d
      · have hpair := candidateA_two_high_residue_sum_le h hy hw hyw hyhigh hwhigh
        omega
      · omega
    · by_cases hwhigh : b g d < w % M g d
      · omega
      · omega


/-- Algebraic form of the lower bound for a triple using the first element of `B_q`. -/
theorem sameBlockLowerBound_eq (g d q : Nat) (hd : 2 <= d) :
    (q * M g d + a g d) + 1 + g = q * M g d + (2 * g + d - 1) := by
  unfold a
  omega

/-- The smallest triple using a `B_q` element and `1,g` is above the top of `B_q`. -/
theorem sameBlockLowerBound_gt_blockEnd (g d q : Nat) (hd : 2 <= d) :
    q * M g d + b g d < (q * M g d + a g d) + 1 + g := by
  rw [sameBlockLowerBound_eq g d q hd]
  unfold b
  omega

/--
Any block element, together with `1` and `g`, already exceeds every element of
the same block.
-/
theorem sameBlockTerm_exceeds_blockEnd {g d q x : Nat}
    (h : Params g d) (hx : InBlock g d q x) :
    q * M g d + b g d < x + 1 + g := by
  have hmin : q * M g d + b g d < (q * M g d + a g d) + 1 + g :=
    sameBlockLowerBound_gt_blockEnd g d q h.d_ge_two
  have hx_lower : q * M g d + a g d <= x := hx.1
  omega

/-- Same-block version used in the periodic safety argument. -/
theorem sameBlockTerm_exceeds_sameBlockTarget {g d q x z : Nat}
    (h : Params g d) (hx : InBlock g d q x) (hz : InBlock g d q z) :
    z < x + 1 + g := by
  have htop : z <= q * M g d + b g d := hz.2
  have hbig : q * M g d + b g d < x + 1 + g :=
    sameBlockTerm_exceeds_blockEnd h hx
  omega

/--
Prefix safety arithmetic: before `z <= 2g+d`, the triple `1,g,g+d` is already
too large.
-/
theorem prefixTripleLowerBound_gt {g d z : Nat} (_h : Params g d)
    (hz : InInterval (g + d + 1) (2 * g + d) z) :
    z < 1 + g + (g + d) := by
  have hz_upper : z <= 2 * g + d := hz.2
  omega

/-- Full prefix safety statement for Theorem A. -/
theorem theoremA_prefix_safe {g d z : Nat} (h : Params g d)
    (hz : InInterval (g + d + 1) (2 * g + d) z) :
    ¬ TripleSumFrom (CandidateA g d) z := by
  intro htriple
  rcases htriple with ⟨x, y, w, hx, hy, hw, hxy, hyw, _hwz, hsum⟩
  have hlo : 1 + g + (g + d) <= x + y + w :=
    candidateA_triple_ge_seed_sum h hx hy hw hxy hyw
  have hhi : z < 1 + g + (g + d) := prefixTripleLowerBound_gt h hz
  omega

/--
Periodic block safety for Theorem A: a candidate in any positive block cannot
be a sum of three distinct smaller candidates.  The proof uses only residues:
the three candidate residues have sum strictly between the target residue and
one full modulus above it.
-/
theorem theoremA_periodic_block_safe {g d q z : Nat} (h : Params g d)
    (_hq : 1 <= q) (hz : InBlock g d q z) :
    ¬ TripleSumFrom (CandidateA g d) z := by
  intro htriple
  rcases htriple with ⟨x, y, w, hx, hy, hw, hxy, hyw, _hwz, hsum⟩
  let s := x % M g d + y % M g d + w % M g d
  let r := z % M g d
  have hmod : s % M g d = r := by
    dsimp [s, r]
    exact triple_sum_mod hsum
  have hzres := block_mod_interval h hz
  have hrlo : a g d <= r := by
    dsimp [r]
    exact hzres.1
  have hrhi : r <= b g d := by
    dsimp [r]
    exact hzres.2
  have hslo : 1 + g + a g d <= s := by
    dsimp [s]
    exact candidateA_ordered_residue_sum_lower h hx hy hw hxy hyw
  have hshi : s <= (b g d + 2) + (b g d + 1) + b g d := by
    dsimp [s]
    exact candidateA_ordered_residue_sum_upper h hx hy hw hxy hyw
  have hr_lt_s : r < s := by
    have hd := h.d_ge_two
    unfold a b at *
    omega
  have hdiff : s - r < M g d := by
    have hd := h.d_ge_two
    have hg := h.three_le_g
    unfold a b M at *
    omega
  exact mod_eq_forbidden_between hmod hr_lt_s hdiff

/-- Prefix-gap coverage from the interval `1 + g + H`. -/
theorem theoremA_prefix_gap_cover_one {g d z : Nat} (h : Params g d)
    (hz : InInterval (2 * g + d + 1) (3 * g + d + 1) z) :
    TripleSumFrom (CandidateA g d) z := by
  let w := z - (1 + g)
  have hzl := hz.1
  have hzu := hz.2
  have hwlo : g + d <= w := by
    dsimp [w]
    apply Nat.le_sub_of_add_le
    omega
  have hwhi : w <= 2 * g + d := by
    dsimp [w]
    rw [Nat.sub_le_iff_le_add]
    omega
  have hwH : InInterval (g + d) (2 * g + d) w := ⟨hwlo, hwhi⟩
  have hsum : 1 + g + w = z := by
    dsimp [w]
    have hle : 1 + g <= z := by omega
    exact Nat.add_sub_of_le hle
  refine
    ⟨1, g, w, candidateA_one g d, candidateA_g g d, candidateA_of_H hwH,
      ?_, ?_, ?_, hsum⟩
  · have hg := h.three_le_g
    omega
  · have hd := h.d_ge_two
    omega
  · omega

theorem H_pair_sum_distinct {g d t : Nat} (_h : Params g d)
    (ht : InInterval (2 * (g + d) + 1) (2 * (2 * g + d) - 1) t) :
    ∃ u v : Nat,
      InInterval (g + d) (2 * g + d) u ∧
      InInterval (g + d) (2 * g + d) v ∧
      u < v ∧ u + v = t := by
  let L := g + d
  let U := 2 * g + d
  have hLleU : L <= U := by
    dsimp [L, U]
    omega
  have htlo : 2 * L + 1 <= t := by
    dsimp [L]
    exact ht.1
  have hthi : t <= 2 * U - 1 := by
    dsimp [U]
    exact ht.2
  by_cases hmid : t <= L + U
  · let u := L
    let v := t - L
    have hvlo : L <= v := by
      dsimp [v]
      apply Nat.le_sub_of_add_le
      omega
    have hvhi : v <= U := by
      dsimp [v]
      rw [Nat.sub_le_iff_le_add]
      omega
    have huv : u < v := by
      dsimp [u, v]
      have : L + 1 <= t - L := by
        apply Nat.le_sub_of_add_le
        omega
      omega
    have hsum : u + v = t := by
      dsimp [u, v]
      have hLt : L <= t := by omega
      exact Nat.add_sub_of_le hLt
    refine ⟨u, v, ?_, ?_, huv, hsum⟩
    · dsimp [u, L, U]
      constructor <;> omega
    · dsimp [L, U] at hvlo hvhi
      exact ⟨hvlo, hvhi⟩
  · let u := t - U
    let v := U
    have hUleT : U <= t := by
      have hgt : L + U < t := by omega
      omega
    have hulo : L <= u := by
      dsimp [u]
      apply Nat.le_sub_of_add_le
      omega
    have huhi : u <= U := by
      dsimp [u]
      rw [Nat.sub_le_iff_le_add]
      omega
    have huv : u < v := by
      dsimp [u, v]
      have hlt : t - U < U := by omega
      exact hlt
    have hsum : u + v = t := by
      dsimp [u, v]
      exact Nat.sub_add_cancel hUleT
    refine ⟨u, v, ?_, ?_, huv, hsum⟩
    · dsimp [L, U] at hulo huhi
      exact ⟨hulo, huhi⟩
    · dsimp [v, L, U]
      constructor <;> omega

/-- Prefix-gap coverage from the interval `1 + (H + H)_distinct`. -/
theorem theoremA_prefix_gap_cover_two {g d z : Nat} (h : Params g d)
    (hz : InInterval (2 * g + 2 * d + 2) (4 * g + 2 * d) z) :
    TripleSumFrom (CandidateA g d) z := by
  let t := z - 1
  have hzl := hz.1
  have hzu := hz.2
  have ht : InInterval (2 * (g + d) + 1) (2 * (2 * g + d) - 1) t := by
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
    ⟨1, u, v, candidateA_one g d, candidateA_of_H hu, candidateA_of_H hv,
      ?_, huv, ?_, hsum⟩
  · have ulo := hu.1
    have hg := h.three_le_g
    have hd := h.d_ge_two
    omega
  · omega

/-- Prefix-gap coverage from the interval `g + (H + H)_distinct`. -/
theorem theoremA_prefix_gap_cover_three {g d z : Nat} (h : Params g d)
    (hz : InInterval (3 * g + 2 * d + 1) (5 * g + 2 * d - 1) z) :
    TripleSumFrom (CandidateA g d) z := by
  let t := z - g
  have hzl := hz.1
  have hzu := hz.2
  have ht : InInterval (2 * (g + d) + 1) (2 * (2 * g + d) - 1) t := by
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
    ⟨g, u, v, candidateA_g g d, candidateA_of_H hu, candidateA_of_H hv,
      ?_, huv, ?_, hsum⟩
  · have ulo := hu.1
    have hd := h.d_ge_two
    omega
  · omega

theorem H_triple_sum_distinct {g d t : Nat} (h : Params g d)
    (ht : InInterval (3 * (g + d) + 3) (3 * (2 * g + d) - 3) t) :
    ∃ u v w : Nat,
      InInterval (g + d) (2 * g + d) u ∧
      InInterval (g + d) (2 * g + d) v ∧
      InInterval (g + d) (2 * g + d) w ∧
      u < v ∧ v < w ∧ u + v + w = t := by
  let L := g + d
  let T := t - 3 * L
  have hg := h.three_le_g
  have hT_eq : 3 * L + T = t := by
    dsimp [T]
    have hle : 3 * L <= t := by
      have htl := ht.1
      omega
    exact Nat.add_sub_of_le hle
  have hTlo : 3 <= T := by
    dsimp [T]
    apply Nat.le_sub_of_add_le
    have htl := ht.1
    omega
  have hThi : T <= 3 * g - 3 := by
    dsimp [T]
    rw [Nat.sub_le_iff_le_add]
    have htu := ht.2
    omega
  by_cases hcase1 : T <= g + 1
  · let u := L
    let v := L + 1
    let w := L + (T - 1)
    have hTminus : T - 1 <= g := by omega
    have horder : u < v ∧ v < w := by
      dsimp [u, v, w]
      omega
    have hsum : u + v + w = t := by
      dsimp [u, v, w]
      omega
    refine ⟨u, v, w, ?_, ?_, ?_, horder.1, horder.2, hsum⟩
    · dsimp [u, L]
      constructor <;> omega
    · dsimp [v, L]
      constructor <;> omega
    · dsimp [w, L]
      constructor <;> omega
  · by_cases hcase2 : T <= 2 * g - 1
    · let u := L
      let v := L + (T - g)
      let w := L + g
      have hTg_lo : 1 <= T - g := by
        apply Nat.le_sub_of_add_le
        omega
      have hTg_hi : T - g <= g := by
        rw [Nat.sub_le_iff_le_add]
        omega
      have horder : u < v ∧ v < w := by
        dsimp [u, v, w]
        have hlt : T - g < g := by omega
        omega
      have hsum : u + v + w = t := by
        dsimp [u, v, w]
        omega
      refine ⟨u, v, w, ?_, ?_, ?_, horder.1, horder.2, hsum⟩
      · dsimp [u, L]
        constructor <;> omega
      · dsimp [v, L]
        constructor <;> omega
      · dsimp [w, L]
        constructor <;> omega
    · let u := L + (T - (2 * g - 1))
      let v := L + (g - 1)
      let w := L + g
      have hT2g_le_g : T - (2 * g - 1) <= g := by omega
      have hT2g_lt_g_minus : T - (2 * g - 1) < g - 1 := by omega
      have horder : u < v ∧ v < w := by
        dsimp [u, v, w]
        omega
      have hsum : u + v + w = t := by
        dsimp [u, v, w]
        omega
      refine ⟨u, v, w, ?_, ?_, ?_, horder.1, horder.2, hsum⟩
      · dsimp [u, L]
        constructor <;> omega
      · dsimp [v, L]
        constructor <;> omega
      · dsimp [w, L]
        constructor <;> omega

/-- Prefix-gap coverage from the interval `(H + H + H)_distinct`. -/
theorem theoremA_prefix_gap_cover_four {g d z : Nat} (h : Params g d)
    (hz : InInterval (3 * (g + d) + 3) (3 * (2 * g + d) - 3) z) :
    TripleSumFrom (CandidateA g d) z := by
  rcases H_triple_sum_distinct h hz with ⟨u, v, w, hu, hv, hw, huv, hvw, hsum⟩
  refine
    ⟨u, v, w, candidateA_of_H hu, candidateA_of_H hv, candidateA_of_H hw,
      huv, hvw, ?_, hsum⟩
  omega

/-- Endpoint inequality used in the first prefix-gap coverage. -/
theorem prefixGap_overlap_one {g d : Nat} (h : Params g d) :
    2 * g + 2 * d + 2 <= 3 * g + d + 2 := by
  have hdg := h.d_le_g
  omega

/-- Endpoint inequality used in the first prefix-gap coverage. -/
theorem prefixGap_overlap_two {g d : Nat} (_h : Params g d) :
    3 * g + 2 * d + 1 <= 4 * g + 2 * d + 1 := by
  omega

/-- Endpoint inequality used in the first prefix-gap coverage. -/
theorem prefixGap_overlap_three {g d : Nat} (h : Params g d) :
    3 * g + 3 * d + 3 <= 5 * g + 2 * d := by
  have hdg := h.d_le_g
  have hg3 := h.three_le_g
  omega

/--
Full prefix-gap coverage for Theorem A.  Every integer between the end of the
prefix and the first periodic block is a sum of three distinct smaller
candidate elements.
-/
theorem theoremA_prefix_gap_covered {g d z : Nat} (h : Params g d)
    (hz : InInterval (2 * g + d + 1) (M g d + a g d - 1) z) :
    TripleSumFrom (CandidateA g d) z := by
  have hzl := hz.1
  have hzu := hz.2
  by_cases h1 : z <= 3 * g + d + 1
  · exact theoremA_prefix_gap_cover_one h ⟨hzl, h1⟩
  · by_cases h2 : z <= 4 * g + 2 * d
    · have hlo2 : 2 * g + 2 * d + 2 <= z := by
        have hdg := h.d_le_g
        omega
      exact theoremA_prefix_gap_cover_two h ⟨hlo2, h2⟩
    · by_cases h3 : z <= 5 * g + 2 * d - 1
      · have hlo3 : 3 * g + 2 * d + 1 <= z := by
          omega
        exact theoremA_prefix_gap_cover_three h ⟨hlo3, h3⟩
      · have hlo4 : 3 * (g + d) + 3 <= z := by
          have hover := prefixGap_overlap_three h
          omega
        have hhi4 : z <= 3 * (2 * g + d) - 3 := by
          have hg := h.three_le_g
          have hd := h.d_ge_two
          unfold M a at hzu
          omega
        exact theoremA_prefix_gap_cover_four h ⟨hlo4, hhi4⟩

/-- Periodic-gap coverage from the interval `1 + g + B_q`. -/
theorem theoremA_periodic_gap_cover_one {g d q z : Nat} (h : Params g d)
    (hq : 1 <= q)
    (hz : InInterval (q * M g d + (2 * g + d - 1))
      (q * M g d + (3 * g + d - 1)) z) :
    TripleSumFrom (CandidateA g d) z := by
  let w := z - (1 + g)
  have hzl := hz.1
  have hzu := hz.2
  have hwlo : q * M g d + a g d <= w := by
    dsimp [w]
    apply Nat.le_sub_of_add_le
    have hd := h.d_ge_two
    unfold a at *
    omega
  have hwhi : w <= q * M g d + b g d := by
    dsimp [w]
    rw [Nat.sub_le_iff_le_add]
    have hd := h.d_ge_two
    unfold b at *
    omega
  have hwB : InBlock g d q w := ⟨hwlo, hwhi⟩
  have hsum : 1 + g + w = z := by
    dsimp [w]
    have hle : 1 + g <= z := by
      have hg := h.three_le_g
      omega
    exact Nat.add_sub_of_le hle
  refine
    ⟨1, g, w, candidateA_one g d, candidateA_g g d,
      candidateA_of_block hq hwB, ?_, ?_, ?_, hsum⟩
  · have hg := h.three_le_g
    omega
  · exact prefix_lt_positive_block h hq (Or.inr (Or.inl rfl)) hwB
  · omega

/-- Periodic-gap coverage from the interval `1 + H + B_q`. -/
theorem theoremA_periodic_gap_cover_two {g d q z : Nat} (h : Params g d)
    (hq : 1 <= q)
    (hz : InInterval (q * M g d + (2 * g + 2 * d - 1))
      (q * M g d + (4 * g + 2 * d - 1)) z) :
    TripleSumFrom (CandidateA g d) z := by
  let T := z - (q * M g d + 1)
  have hzl := hz.1
  have hzu := hz.2
  have hT_eq : q * M g d + 1 + T = z := by
    dsimp [T]
    have hle : q * M g d + 1 <= z := by
      have hd := h.d_ge_two
      omega
    exact Nat.add_sub_of_le hle
  have hTlo : a g d + (g + d) <= T := by
    dsimp [T]
    apply Nat.le_sub_of_add_le
    have hd := h.d_ge_two
    unfold a at *
    omega
  have hThi : T <= b g d + (2 * g + d) := by
    dsimp [T]
    rw [Nat.sub_le_iff_le_add]
    have hd := h.d_ge_two
    unfold b at *
    omega
  by_cases hlow : T <= b g d + (g + d)
  · let u := g + d
    let r := T - u
    let w := q * M g d + r
    have hrlo : a g d <= r := by
      dsimp [r, u]
      apply Nat.le_sub_of_add_le
      exact hTlo
    have hrhi : r <= b g d := by
      dsimp [r, u]
      rw [Nat.sub_le_iff_le_add]
      exact hlow
    have huH : InInterval (g + d) (2 * g + d) u := by
      dsimp [u]
      constructor <;> omega
    have hwB : InBlock g d q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨hrlo, hrhi⟩
    have hsumr : u + r = T := by
      dsimp [r]
      have huT : u <= T := by
        have ha := a_ge_one h
        omega
      exact Nat.add_sub_of_le huT
    have hsum : 1 + u + w = z := by
      dsimp [w]
      omega
    refine
      ⟨1, u, w, candidateA_one g d, candidateA_of_H huH,
        candidateA_of_block hq hwB, ?_, ?_, ?_, hsum⟩
    · dsimp [u]
      have hg := h.three_le_g
      have hd := h.d_ge_two
      omega
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr huH)) hwB
    · omega
  · let u := T - b g d
    let w := q * M g d + b g d
    have hbT : b g d <= T := by
      have ha := a_ge_one h
      omega
    have hulo : g + d <= u := by
      dsimp [u]
      apply Nat.le_sub_of_add_le
      omega
    have huhi : u <= 2 * g + d := by
      dsimp [u]
      rw [Nat.sub_le_iff_le_add]
      omega
    have huH : InInterval (g + d) (2 * g + d) u := ⟨hulo, huhi⟩
    have hwB : InBlock g d q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨blockStart_le_blockEnd h, Nat.le_refl _⟩
    have hsumb : b g d + u = T := by
      dsimp [u]
      exact Nat.add_sub_of_le hbT
    have hsum : 1 + u + w = z := by
      dsimp [w]
      omega
    refine
      ⟨1, u, w, candidateA_one g d, candidateA_of_H huH,
        candidateA_of_block hq hwB, ?_, ?_, ?_, hsum⟩
    · have ulo := huH.1
      have hg := h.three_le_g
      have hd := h.d_ge_two
      omega
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr huH)) hwB
    · omega

/-- Periodic-gap coverage from the interval `g + H + B_q`. -/
theorem theoremA_periodic_gap_cover_three {g d q z : Nat} (h : Params g d)
    (hq : 1 <= q)
    (hz : InInterval (q * M g d + (3 * g + 2 * d - 2))
      (q * M g d + (5 * g + 2 * d - 2)) z) :
    TripleSumFrom (CandidateA g d) z := by
  let T := z - (q * M g d + g)
  have hzl := hz.1
  have hzu := hz.2
  have hT_eq : q * M g d + g + T = z := by
    dsimp [T]
    have hle : q * M g d + g <= z := by
      have hd := h.d_ge_two
      have hg := h.three_le_g
      omega
    exact Nat.add_sub_of_le hle
  have hTlo : a g d + (g + d) <= T := by
    dsimp [T]
    apply Nat.le_sub_of_add_le
    have hd := h.d_ge_two
    unfold a at *
    omega
  have hThi : T <= b g d + (2 * g + d) := by
    dsimp [T]
    rw [Nat.sub_le_iff_le_add]
    have hd := h.d_ge_two
    unfold b at *
    omega
  by_cases hlow : T <= b g d + (g + d)
  · let u := g + d
    let r := T - u
    let w := q * M g d + r
    have hrlo : a g d <= r := by
      dsimp [r, u]
      apply Nat.le_sub_of_add_le
      exact hTlo
    have hrhi : r <= b g d := by
      dsimp [r, u]
      rw [Nat.sub_le_iff_le_add]
      exact hlow
    have huH : InInterval (g + d) (2 * g + d) u := by
      dsimp [u]
      constructor <;> omega
    have hwB : InBlock g d q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨hrlo, hrhi⟩
    have hsumr : u + r = T := by
      dsimp [r]
      have huT : u <= T := by
        have ha := a_ge_one h
        omega
      exact Nat.add_sub_of_le huT
    have hsum : g + u + w = z := by
      dsimp [w]
      omega
    refine
      ⟨g, u, w, candidateA_g g d, candidateA_of_H huH,
        candidateA_of_block hq hwB, ?_, ?_, ?_, hsum⟩
    · dsimp [u]
      have hd := h.d_ge_two
      omega
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr huH)) hwB
    · have hg := h.three_le_g
      omega
  · let u := T - b g d
    let w := q * M g d + b g d
    have hbT : b g d <= T := by
      have ha := a_ge_one h
      omega
    have hulo : g + d <= u := by
      dsimp [u]
      apply Nat.le_sub_of_add_le
      omega
    have huhi : u <= 2 * g + d := by
      dsimp [u]
      rw [Nat.sub_le_iff_le_add]
      omega
    have huH : InInterval (g + d) (2 * g + d) u := ⟨hulo, huhi⟩
    have hwB : InBlock g d q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨blockStart_le_blockEnd h, Nat.le_refl _⟩
    have hsumb : b g d + u = T := by
      dsimp [u]
      exact Nat.add_sub_of_le hbT
    have hsum : g + u + w = z := by
      dsimp [w]
      omega
    refine
      ⟨g, u, w, candidateA_g g d, candidateA_of_H huH,
        candidateA_of_block hq hwB, ?_, ?_, ?_, hsum⟩
    · have ulo := huH.1
      have hd := h.d_ge_two
      omega
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr huH)) hwB
    · have hg := h.three_le_g
      omega

/-- Periodic-gap coverage from the interval `(H + H)_distinct + B_q`. -/
theorem theoremA_periodic_gap_cover_four {g d q z : Nat} (h : Params g d)
    (hq : 1 <= q)
    (hz : InInterval (q * M g d + (3 * g + 3 * d - 1))
      (q * M g d + (6 * g + 3 * d - 3)) z) :
    TripleSumFrom (CandidateA g d) z := by
  let T := z - q * M g d
  have hzl := hz.1
  have hzu := hz.2
  have hT_eq : q * M g d + T = z := by
    dsimp [T]
    have hle : q * M g d <= z := by
      have hd := h.d_ge_two
      omega
    exact Nat.add_sub_of_le hle
  have hTlo : a g d + (2 * (g + d) + 1) <= T := by
    dsimp [T]
    apply Nat.le_sub_of_add_le
    have hd := h.d_ge_two
    unfold a at *
    omega
  have hThi : T <= b g d + (2 * (2 * g + d) - 1) := by
    dsimp [T]
    rw [Nat.sub_le_iff_le_add]
    have hd := h.d_ge_two
    unfold b at *
    omega
  by_cases hlow : T <= b g d + (2 * (g + d) + 1)
  · let u := g + d
    let v := g + d + 1
    let r := T - (2 * (g + d) + 1)
    let w := q * M g d + r
    have hrlo : a g d <= r := by
      dsimp [r]
      apply Nat.le_sub_of_add_le
      exact hTlo
    have hrhi : r <= b g d := by
      dsimp [r]
      rw [Nat.sub_le_iff_le_add]
      omega
    have huH : InInterval (g + d) (2 * g + d) u := by
      dsimp [u]
      constructor <;> omega
    have hvH : InInterval (g + d) (2 * g + d) v := by
      dsimp [v]
      constructor
      · omega
      · have hg := h.three_le_g
        omega
    have hwB : InBlock g d q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨hrlo, hrhi⟩
    have hpair : u + v = 2 * (g + d) + 1 := by
      dsimp [u, v]
      omega
    have hsumr : (2 * (g + d) + 1) + r = T := by
      dsimp [r]
      have hPloT : 2 * (g + d) + 1 <= T := by
        have ha := a_ge_one h
        omega
      exact Nat.add_sub_of_le hPloT
    have hsum : u + v + w = z := by
      dsimp [w]
      omega
    refine
      ⟨u, v, w, candidateA_of_H huH, candidateA_of_H hvH,
        candidateA_of_block hq hwB, ?_, ?_, ?_, hsum⟩
    · dsimp [u, v]
      omega
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr hvH)) hwB
    · have hg := h.three_le_g
      omega
  · let p := T - b g d
    let w := q * M g d + b g d
    have hbT : b g d <= T := by
      omega
    have hplo : 2 * (g + d) + 1 <= p := by
      dsimp [p]
      apply Nat.le_sub_of_add_le
      omega
    have hphi : p <= 2 * (2 * g + d) - 1 := by
      dsimp [p]
      rw [Nat.sub_le_iff_le_add]
      omega
    have hLU : g + d < 2 * g + d := by
      have hg := h.three_le_g
      omega
    have hp : NatInterval (2 * (g + d) + 1) (2 * (2 * g + d) - 1) p :=
      ⟨hplo, hphi⟩
    rcases interval_pair_sum_distinct hLU hp with
      ⟨u, v, huH, hvH, huv, hsumuv⟩
    have hwB : InBlock g d q w := by
      dsimp [w]
      exact inBlock_of_residue_interval ⟨blockStart_le_blockEnd h, Nat.le_refl _⟩
    have hsumb : b g d + p = T := by
      dsimp [p]
      exact Nat.add_sub_of_le hbT
    have hsum : u + v + w = z := by
      dsimp [w]
      omega
    refine
      ⟨u, v, w, candidateA_of_H huH, candidateA_of_H hvH,
        candidateA_of_block hq hwB, huv, ?_, ?_, hsum⟩
    · exact prefix_lt_positive_block h hq (Or.inr (Or.inr hvH)) hwB
    · have hg := h.three_le_g
      omega

/-- Endpoint inequalities used in periodic-gap coverage. -/
theorem periodicGap_overlap_one {g d : Nat} (h : Params g d) :
    2 * g + 2 * d - 1 <= 3 * g + d := by
  have hdg := h.d_le_g
  omega

theorem periodicGap_overlap_two {g d : Nat} (_h : Params g d) :
    3 * g + 2 * d - 2 <= 4 * g + 2 * d := by
  omega

theorem periodicGap_overlap_three {g d : Nat} (h : Params g d) :
    3 * g + 3 * d - 1 <= 5 * g + 2 * d - 1 := by
  have hdg := h.d_le_g
  omega

/--
Full periodic-gap coverage for Theorem A.  Every integer between a positive
periodic block and the next periodic block is a sum of three distinct smaller
candidate elements.
-/
theorem theoremA_periodic_gap_covered {g d q z : Nat} (h : Params g d)
    (hq : 1 <= q)
    (hz : InInterval (q * M g d + b g d + 1)
      ((q + 1) * M g d + a g d - 1) z) :
    TripleSumFrom (CandidateA g d) z := by
  have hzl := hz.1
  have hzu := hz.2
  by_cases h1 : z <= q * M g d + (3 * g + d - 1)
  · have hlo1 : q * M g d + (2 * g + d - 1) <= z := by
      have hd := h.d_ge_two
      unfold b at hzl
      omega
    exact theoremA_periodic_gap_cover_one h hq ⟨hlo1, h1⟩
  · by_cases h2 : z <= q * M g d + (4 * g + 2 * d - 1)
    · have hlo2 : q * M g d + (2 * g + 2 * d - 1) <= z := by
        have hover := periodicGap_overlap_one h
        omega
      exact theoremA_periodic_gap_cover_two h hq ⟨hlo2, h2⟩
    · by_cases h3 : z <= q * M g d + (5 * g + 2 * d - 2)
      · have hlo3 : q * M g d + (3 * g + 2 * d - 2) <= z := by
          have hover := periodicGap_overlap_two h
          omega
        exact theoremA_periodic_gap_cover_three h hq ⟨hlo3, h3⟩
      · have hlo4 : q * M g d + (3 * g + 3 * d - 1) <= z := by
          have hover := periodicGap_overlap_three h
          omega
        have hhi4 : z <= q * M g d + (6 * g + 3 * d - 3) := by
          have hupper :
              (q + 1) * M g d + a g d - 1 =
                q * M g d + (6 * g + 3 * d - 3) := by
            rw [Nat.add_mul, Nat.one_mul]
            have hd := h.d_ge_two
            unfold M a
            omega
          omega
        exact theoremA_periodic_gap_cover_four h hq ⟨hlo4, hhi4⟩

/--
Combined candidate-gap coverage for Theorem A.  This packages the prefix gap
and every periodic gap into one coverage statement.
-/
theorem theoremA_candidate_gap_covered {g d z : Nat} (h : Params g d)
    (hz : InInterval (2 * g + d + 1) (M g d + a g d - 1) z ∨
      ∃ q : Nat, 1 <= q ∧
        InInterval (q * M g d + b g d + 1)
          ((q + 1) * M g d + a g d - 1) z) :
    TripleSumFrom (CandidateA g d) z := by
  rcases hz with hzprefix | hzperiodic
  · exact theoremA_prefix_gap_covered h hzprefix
  · rcases hzperiodic with ⟨q, hq, hzq⟩
    exact theoremA_periodic_gap_covered h hq hzq

/--
Every omitted integer above `g + d` lies in one of the candidate gaps and is
therefore covered by a triple of distinct smaller candidate elements.
-/
theorem theoremA_omitted_gt_g_add_d_covered {g d z : Nat} (h : Params g d)
    (hzgt : g + d < z) (hzomitted : ¬ CandidateA g d z) :
    TripleSumFrom (CandidateA g d) z := by
  have hnotPrefix : ¬ InPrefix g d z := by
    intro hp
    exact hzomitted (Or.inl hp)
  have hz_after_prefix : 2 * g + d + 1 <= z := by
    by_cases hle : z <= 2 * g + d
    · have hp : InPrefix g d z := by
        unfold InPrefix InInterval
        exact Or.inr (Or.inr ⟨by omega, hle⟩)
      exact False.elim (hnotPrefix hp)
    · omega
  by_cases hfirst : z <= M g d + a g d - 1
  · exact theoremA_prefix_gap_covered h ⟨hz_after_prefix, hfirst⟩
  · let q := z / M g d
    let r := z % M g d
    have hMpos : 0 < M g d := by
      have hg := h.three_le_g
      have hd := h.d_ge_two
      unfold M
      omega
    have hz_ge_first : M g d + a g d <= z := by
      omega
    have hqpos : 1 <= q := by
      dsimp [q]
      apply Nat.div_pos
      · have ha := a_ge_one h
        omega
      · exact hMpos
    have hrM : r < M g d := by
      dsimp [r]
      exact Nat.mod_lt z hMpos
    have hz_eq : z = q * M g d + r := by
      dsimp [q, r]
      simpa [Nat.mul_comm] using (Nat.div_add_mod z (M g d)).symm
    by_cases hra : r < a g d
    · have hqtwo : 2 <= q := by
        by_cases hqone : q = 1
        · have hlt_first : z < M g d + a g d := by
            rw [hz_eq, hqone]
            omega
          omega
        · omega
      have hqprev : 1 <= q - 1 := by
        omega
      have hzgap :
          InInterval ((q - 1) * M g d + b g d + 1)
            (((q - 1) + 1) * M g d + a g d - 1) z := by
        constructor
        · have hq_mul : q * M g d = (q - 1) * M g d + M g d := by
            have hq_eq : (q - 1) + 1 = q := by omega
            calc
              q * M g d = ((q - 1) + 1) * M g d := by rw [hq_eq]
              _ = (q - 1) * M g d + 1 * M g d := by rw [Nat.add_mul]
              _ = (q - 1) * M g d + M g d := by rw [Nat.one_mul]
          rw [hz_eq, hq_mul]
          have hbM := b_lt_M h
          omega
        · rw [hz_eq]
          have hq_eq : (q - 1) + 1 = q := by omega
          rw [hq_eq]
          have ha := a_ge_one h
          omega
      exact theoremA_periodic_gap_covered h hqprev hzgap
    · have har : a g d <= r := by omega
      by_cases hrb : r <= b g d
      · have hblock : InBlock g d q z := by
          rw [hz_eq]
          exact inBlock_of_residue_interval ⟨har, hrb⟩
        exact False.elim (hzomitted (candidateA_of_block hqpos hblock))
      · have hbr : b g d < r := by omega
        have hzgap :
            InInterval (q * M g d + b g d + 1)
              ((q + 1) * M g d + a g d - 1) z := by
          constructor
          · rw [hz_eq]
            omega
          · rw [hz_eq, Nat.add_mul, Nat.one_mul]
            have ha := a_ge_one h
            omega
        exact theoremA_periodic_gap_covered h hqpos hzgap

/--
Every candidate above `g + d` is safe from being a sum of three distinct
smaller candidates.
-/
theorem theoremA_candidate_gt_g_add_d_safe {g d z : Nat} (h : Params g d)
    (hzgt : g + d < z) (hzcandidate : CandidateA g d z) :
    ¬ TripleSumFrom (CandidateA g d) z := by
  unfold CandidateA at hzcandidate
  rcases hzcandidate with hp | hb
  · have hzprefix : InInterval (g + d + 1) (2 * g + d) z := by
      unfold InPrefix InInterval at hp
      rcases hp with rfl | rfl | hzH
      · have hg := h.three_le_g
        have hd := h.d_ge_two
        omega
      · have hd := h.d_ge_two
        omega
      · constructor
        · omega
        · exact hzH.2
    exact theoremA_prefix_safe h hzprefix
  · rcases hb with ⟨q, hq, hzblock⟩
    exact theoremA_periodic_block_safe h hq hzblock

/--
Final exact characterization in Theorem A, above the initial threshold
`g + d`: the candidate set is exactly the set of integers not forbidden by a
triple of distinct smaller candidate elements.
-/
theorem theoremA_exact_characterization {g d z : Nat} (h : Params g d)
    (hzgt : g + d < z) :
    CandidateA g d z ↔ ¬ TripleSumFrom (CandidateA g d) z := by
  constructor
  · intro hzcandidate
    exact theoremA_candidate_gt_g_add_d_safe h hzgt hzcandidate
  · intro hsafe
    by_cases hzcandidate : CandidateA g d z
    · exact hzcandidate
    · exact False.elim (hsafe (theoremA_omitted_gt_g_add_d_covered h hzgt hzcandidate))

/-- Initial seed for Theorem A before the recursive greedy rule starts. -/
def TheoremASeed (g d z : Nat) : Prop :=
  z = 1 ∨ z = g ∨ z = g + d

/-- The explicit candidate set has exactly the three Theorem A seed values up to `g+d`. -/
theorem theoremA_candidate_seed_prefix {g d z : Nat} (h : Params g d)
    (hzle : z <= g + d) :
    CandidateA g d z ↔ TheoremASeed g d z := by
  constructor
  · intro hz
    unfold CandidateA at hz
    rcases hz with hp | hb
    · unfold InPrefix InInterval at hp
      rcases hp with h1 | hg | hH
      · exact Or.inl h1
      · exact Or.inr (Or.inl hg)
      · exact Or.inr (Or.inr (by omega))
    · rcases hb with ⟨q, hq, hzblock⟩
      have hMz : M g d <= z := positive_block_ge_M hq hzblock
      have hltM : g + d < M g d := by
        have hg := h.three_le_g
        have hd := h.d_ge_two
        unfold M
        omega
      exact False.elim (by omega)
  · intro hs
    unfold TheoremASeed at hs
    rcases hs with h1 | hg | hgd
    · rw [h1]
      exact candidateA_one g d
    · rw [hg]
      exact candidateA_g g d
    · rw [hgd]
      exact candidateA_of_H (by
        unfold InInterval
        constructor <;> omega)

/-- Theorem A's exact characterization is the recursive greedy step after the seed. -/
theorem theoremA_candidate_recursive_step {g d z : Nat} (h : Params g d)
    (hzgt : g + d < z) :
    RecursiveGreedyStep (CandidateA g d) z := by
  unfold RecursiveGreedyStep GreedyAdmissible
  exact theoremA_exact_characterization h hzgt

/-- The candidate set satisfies the seeded recursive greedy criterion for Theorem A. -/
theorem theoremA_candidate_seededGreedySet {g d : Nat} (h : Params g d) :
    SeededGreedySet (TheoremASeed g d) (CandidateA g d) (g + d) := by
  constructor
  · intro z hzle
    exact theoremA_candidate_seed_prefix h hzle
  · intro z hzgt
    exact theoremA_candidate_recursive_step h hzgt

/--
Consequently, any set satisfying the same Theorem A seed and recursive greedy
criterion is extensionally equal to the explicit candidate set.
-/
theorem theoremA_seededGreedySet_eq_candidate {g d : Nat} (h : Params g d)
    {G : Nat → Prop}
    (hG : SeededGreedySet (TheoremASeed g d) G (g + d)) :
    ∀ z, G z ↔ CandidateA g d z := by
  intro z
  exact seededGreedySet_ext hG (theoremA_candidate_seededGreedySet h) z


end GreedyThreeSumfree
