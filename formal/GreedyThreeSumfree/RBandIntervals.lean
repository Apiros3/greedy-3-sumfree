import GreedyThreeSumfree.IntervalSumWitnesses
import GreedyThreeSumfree.RBandBasic

namespace GreedyThreeSumfree
namespace RBand

theorem e_lt_h {r h e : Nat} (hp : Params r h e) : e < h := by
  have hh := hp.h_ge_six
  have he := hp.e_le_h_sub_two
  omega

theorem prev_grid_add_one_le_D {r h e : Nat} (hp : Params r h e) :
    (2 * r - 1) * h + 1 <= D r h e := by
  unfold D
  have he := hp.e_pos
  omega

theorem prev_grid_lt_D {r h e : Nat} (hp : Params r h e) :
    (2 * r - 1) * h < D r h e := by
  have hle := prev_grid_add_one_le_D hp
  omega

theorem D_add_two_le_next_grid {r h e : Nat} (hp : Params r h e) :
    D r h e + 2 <= 2 * r * h := by
  have hr2 : 2 * r = (2 * r - 1) + 1 := by
    have hr := hp.r_pos
    omega
  calc
    D r h e + 2 = (2 * r - 1) * h + e + 2 := by rfl
    _ <= (2 * r - 1) * h + (h - 2) + 2 := by
      have he := hp.e_le_h_sub_two
      omega
    _ <= (2 * r - 1) * h + h := by
      have hh := hp.h_ge_six
      omega
    _ = ((2 * r - 1) + 1) * h := by
      rw [Nat.add_mul, Nat.one_mul]
    _ = 2 * r * h := by
      rw [← hr2]

theorem D_lt_next_grid {r h e : Nat} (hp : Params r h e) :
    D r h e < 2 * r * h := by
  have hle := D_add_two_le_next_grid hp
  omega

theorem HHi_lt_next_HLo {r h e i : Nat} (hp : Params r h e) :
    HHi r h e i < HLo r h e (i + 1) := by
  have hh := hp.h_ge_six
  unfold HHi HLo
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem ILo_add_two_eq_HLo {r h e i : Nat} (hp : Params r h e) :
    ILo r h e i + 2 = HLo r h e i := by
  have hH := HLo_ge_three (r := r) (h := h) (e := e) (i := i) hp
  unfold ILo
  omega

theorem IHi_add_two_eq_HHi {r h e i : Nat} (hp : Params r h e) :
    IHi r h e i + 2 = HHi r h e i := by
  have hh := hp.h_ge_six
  unfold IHi HHi
  omega

theorem add_two_mem_H_of_mem_I {r h e i x : Nat} (hp : Params r h e)
    (hx : InI r h e i x) : InH r h e i (x + 2) := by
  have hloeq := ILo_add_two_eq_HLo (r := r) (h := h) (e := e) (i := i) hp
  have hhieq := IHi_add_two_eq_HHi (r := r) (h := h) (e := e) (i := i) hp
  unfold InI InInterval at hx
  unfold InH InInterval
  constructor
  · rw [← hloeq]
    omega
  · rw [← hhieq]
    omega

theorem sub_two_mem_I_of_mem_H {r h e i x : Nat} (hp : Params r h e)
    (hx : InH r h e i x) : InI r h e i (x - 2) := by
  unfold InH InInterval at hx
  unfold InI InInterval
  unfold ILo IHi HHi HLo at *
  have hD := D_ge_three hp
  have hh := hp.h_ge_six
  constructor <;> omega

/--
The right-hand interval whose sums with `H_i` give the shifted adjacent
two-sum slice.
-/
def shiftedAdjacentLo (r h e j : Nat) : Nat := HLo r h e j + 2

/--
The right endpoint of the interval whose sums with `H_i` give the shifted
adjacent two-sum slice.
-/
def shiftedAdjacentHi (r h e j : Nat) : Nat := HLo r h e j + 2 * h - 3

/-- Left endpoint of the shifted two-sum slice indexed by `m`. -/
def shiftedPairSliceLo (r h e m : Nat) : Nat := 2 * D r h e + 2 * m * h + 2

/-- Right endpoint of the shifted two-sum slice indexed by `m`. -/
def shiftedPairSliceHi (r h e m : Nat) : Nat := 2 * D r h e + 2 * m * h + 3 * h - 4

/-- Membership in the shifted two-sum slice indexed by `m`. -/
def InShiftedPairSlice (r h e m t : Nat) : Prop :=
  InInterval (shiftedPairSliceLo r h e m) (shiftedPairSliceHi r h e m) t

theorem shiftedAdjacentLo_le_shiftedAdjacentHi {r h e j : Nat} (hp : Params r h e) :
    shiftedAdjacentLo r h e j <= shiftedAdjacentHi r h e j := by
  have hh := hp.h_ge_six
  unfold shiftedAdjacentLo shiftedAdjacentHi HLo
  omega

theorem shiftedPairSlice_nonempty {r h e m : Nat} (hp : Params r h e) :
    shiftedPairSliceLo r h e m <= shiftedPairSliceHi r h e m := by
  have hh := hp.h_ge_six
  unfold shiftedPairSliceLo shiftedPairSliceHi
  omega

theorem shiftedPairSlice_next_lo_le_hi {r h e m : Nat} (hp : Params r h e) :
    shiftedPairSliceLo r h e (m + 1) <= shiftedPairSliceHi r h e m := by
  have hh := hp.h_ge_six
  unfold shiftedPairSliceLo shiftedPairSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem shiftedPairSlice_next_overlap {r h e m : Nat} (hp : Params r h e) :
    ∃ t : Nat,
      InShiftedPairSlice r h e m t ∧ InShiftedPairSlice r h e (m + 1) t := by
  refine ⟨shiftedPairSliceLo r h e (m + 1), ?_, ?_⟩
  · unfold InShiftedPairSlice InInterval
    constructor
    · unfold shiftedPairSliceLo
      simp [Nat.left_distrib, Nat.right_distrib]
    · exact shiftedPairSlice_next_lo_le_hi (r := r) (h := h) (e := e) (m := m) hp
  · unfold InShiftedPairSlice InInterval
    exact ⟨by omega, shiftedPairSlice_nonempty (r := r) (h := h) (e := e) (m := m + 1) hp⟩

/-- A finite chain of overlapping shifted slices covers the interval from the
first left endpoint to the last right endpoint. -/
theorem shiftedPairSlice_chain_cover {r h e a n t : Nat} (hp : Params r h e)
    (ht :
      InInterval (shiftedPairSliceLo r h e a) (shiftedPairSliceHi r h e (a + n)) t) :
    ∃ m : Nat, a <= m ∧ m <= a + n ∧ InShiftedPairSlice r h e m t := by
  induction n with
  | zero =>
      exact ⟨a, by omega, by omega, ht⟩
  | succ n ih =>
      by_cases htn : t <= shiftedPairSliceHi r h e (a + n)
      · rcases ih ⟨ht.1, htn⟩ with ⟨m, hma, hmle, hmem⟩
        exact ⟨m, hma, by omega, hmem⟩
      · have hlo : shiftedPairSliceLo r h e ((a + n) + 1) <= t := by
          have hover :=
            shiftedPairSlice_next_lo_le_hi (r := r) (h := h) (e := e) (m := a + n) hp
          omega
        have hidx : (a + n) + 1 = a + (n + 1) := by omega
        have hhi : t <= shiftedPairSliceHi r h e ((a + n) + 1) := by
          simpa [hidx] using ht.2
        exact ⟨(a + n) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

/--
Every target in the sum interval of two closed intervals has a constructive
two-summand witness.  This is the non-distinct analogue used for sums of two
different r-band intervals.
-/
theorem interval_pair_sum {L1 U1 L2 U2 t : Nat} (h1 : L1 <= U1) (h2 : L2 <= U2)
    (ht : InInterval (L1 + L2) (U1 + U2) t) :
    ∃ u v : Nat, InInterval L1 U1 u ∧ InInterval L2 U2 v ∧ u + v = t := by
  have htlo : L1 + L2 <= t := ht.1
  have hthi : t <= U1 + U2 := ht.2
  by_cases hleft : t <= U1 + L2
  · let u := t - L2
    let v := L2
    have hL2t : L2 <= t := by omega
    have hulo : L1 <= u := by
      dsimp [u]
      apply Nat.le_sub_of_add_le
      omega
    have huhi : u <= U1 := by
      dsimp [u]
      rw [Nat.sub_le_iff_le_add]
      omega
    have hsum : u + v = t := by
      dsimp [u, v]
      exact Nat.sub_add_cancel hL2t
    refine ⟨u, v, ?_, ?_, hsum⟩
    · dsimp [InInterval]
      exact ⟨hulo, huhi⟩
    · dsimp [v, InInterval]
      constructor <;> omega
  · let u := U1
    let v := t - U1
    have hU1t : U1 <= t := by omega
    have hvlo : L2 <= v := by
      dsimp [v]
      apply Nat.le_sub_of_add_le
      omega
    have hvhi : v <= U2 := by
      dsimp [v]
      rw [Nat.sub_le_iff_le_add]
      omega
    have hsum : u + v = t := by
      dsimp [u, v]
      exact Nat.add_sub_of_le hU1t
    refine ⟨u, v, ?_, ?_, hsum⟩
    · dsimp [u, InInterval]
      constructor <;> omega
    · dsimp [InInterval]
      exact ⟨hvlo, hvhi⟩

theorem H_shiftedAdjacent_lo_eq_slice_lo {r h e i j : Nat} :
    HLo r h e i + shiftedAdjacentLo r h e j =
      shiftedPairSliceLo r h e (i + j) := by
  unfold shiftedAdjacentLo shiftedPairSliceLo HLo
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem H_shiftedAdjacent_hi_eq_slice_hi {r h e i j : Nat} (hp : Params r h e) :
    HHi r h e i + shiftedAdjacentHi r h e j =
      shiftedPairSliceHi r h e (i + j) := by
  have hh := hp.h_ge_six
  unfold HHi shiftedAdjacentHi shiftedPairSliceHi HLo
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

/--
For any fixed indices `i,j`, the shifted adjacent two-sums cover the slice
indexed by `i+j`.
-/
theorem shifted_adjacent_pair_sum_of_indices {r h e i j t : Nat} (hp : Params r h e)
    (ht : InShiftedPairSlice r h e (i + j) t) :
    ∃ x y : Nat,
      InH r h e i x ∧
      InInterval (shiftedAdjacentLo r h e j) (shiftedAdjacentHi r h e j) y ∧
      x + y = t := by
  have hH : HLo r h e i <= HHi r h e i := HLo_le_HHi hp
  have hAdj :
      shiftedAdjacentLo r h e j <= shiftedAdjacentHi r h e j :=
    shiftedAdjacentLo_le_shiftedAdjacentHi (r := r) (h := h) (e := e) (j := j) hp
  have hlo := H_shiftedAdjacent_lo_eq_slice_lo (r := r) (h := h) (e := e) (i := i) (j := j)
  have hhi := H_shiftedAdjacent_hi_eq_slice_hi (r := r) (h := h) (e := e) (i := i) (j := j) hp
  have htSum :
      InInterval (HLo r h e i + shiftedAdjacentLo r h e j)
        (HHi r h e i + shiftedAdjacentHi r h e j) t := by
    unfold InShiftedPairSlice at ht
    simpa [hlo, hhi] using ht
  rcases interval_pair_sum hH hAdj htSum with ⟨x, y, hx, hy, hsum⟩
  exact ⟨x, y, hx, hy, hsum⟩

/-- The same coverage with an explicit normalized slice index `m`. -/
theorem shifted_adjacent_pair_sum_of_sum {r h e i j m t : Nat} (hp : Params r h e)
    (hm : i + j = m) (ht : InShiftedPairSlice r h e m t) :
    ∃ x y : Nat,
      InH r h e i x ∧
      InInterval (shiftedAdjacentLo r h e j) (shiftedAdjacentHi r h e j) y ∧
      x + y = t := by
  have ht' : InShiftedPairSlice r h e (i + j) t := by
    simpa [hm] using ht
  exact shifted_adjacent_pair_sum_of_indices
    (r := r) (h := h) (e := e) (i := i) (j := j) hp ht'

/--
For a fixed `m`, choosing `i = 0` and `j = m` gives a constructive witness for
every target in the shifted adjacent slice.
-/
theorem shifted_adjacent_pair_sum_exists {r h e m t : Nat} (hp : Params r h e)
    (ht : InShiftedPairSlice r h e m t) :
    ∃ i j x y : Nat,
      i + j = m ∧
      InH r h e i x ∧
      InInterval (shiftedAdjacentLo r h e j) (shiftedAdjacentHi r h e j) y ∧
      x + y = t := by
  rcases shifted_adjacent_pair_sum_of_sum
      (r := r) (h := h) (e := e) (i := 0) (j := m) (m := m) hp (by omega) ht with
    ⟨x, y, hx, hy, hsum⟩
  exact ⟨0, m, x, y, by omega, hx, hy, hsum⟩

end RBand
end GreedyThreeSumfree
