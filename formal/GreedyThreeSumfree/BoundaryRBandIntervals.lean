import GreedyThreeSumfree.BoundaryRBandBasic

namespace GreedyThreeSumfree
namespace BoundaryRBand

theorem HHi_lt_next_HLo {r h i : Nat} (hp : Params r h) :
    HHi r h i < HLo r h (i + 1) := by
  have hh := hp.h_ge_six
  unfold HHi HLo
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem KLo_add_one_eq_HLo {r h i : Nat} (hp : Params r h) :
    KLo r h i + 1 = HLo r h i := by
  have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
  unfold KLo
  omega

theorem KHi_add_one_eq_HHi {r h i : Nat} (hp : Params r h) :
    KHi r h i + 1 = HHi r h i := by
  have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
  unfold KHi HHi
  omega

theorem add_one_mem_H_of_mem_K {r h i x : Nat} (hp : Params r h)
    (hx : InK r h i x) : InH r h i (x + 1) := by
  have hloeq := KLo_add_one_eq_HLo (r := r) (h := h) (i := i) hp
  have hhieq := KHi_add_one_eq_HHi (r := r) (h := h) (i := i) hp
  unfold InK InInterval at hx
  unfold InH InInterval
  constructor
  · rw [← hloeq]
    omega
  · rw [← hhieq]
    omega

theorem sub_one_mem_K_of_mem_H {r h i x : Nat} (hp : Params r h)
    (hx : InH r h i x) : InK r h i (x - 1) := by
  unfold InH InInterval at hx
  unfold InK InInterval
  unfold KLo KHi HHi HLo at *
  have hD := D_ge_three hp
  have hh := hp.h_ge_six
  constructor <;> omega

/--
The right-hand interval whose sums with `H_i` give the shifted adjacent
two-sum slice.
-/
def shiftedAdjacentLo (r h j : Nat) : Nat := HLo r h j + 2

/--
The right endpoint of the interval whose sums with `H_i` give the shifted
adjacent two-sum slice.
-/
def shiftedAdjacentHi (r h j : Nat) : Nat := HLo r h j + 2 * h - 3

/-- Left endpoint of the shifted two-sum slice indexed by `m`. -/
def shiftedPairSliceLo (r h m : Nat) : Nat := 2 * D r h + 2 * m * h + 2

/-- Right endpoint of the shifted two-sum slice indexed by `m`. -/
def shiftedPairSliceHi (r h m : Nat) : Nat := 2 * D r h + 2 * m * h + 3 * h - 4

/-- Membership in the shifted two-sum slice indexed by `m`. -/
def InShiftedPairSlice (r h m t : Nat) : Prop :=
  InInterval (shiftedPairSliceLo r h m) (shiftedPairSliceHi r h m) t

theorem shiftedAdjacentLo_le_shiftedAdjacentHi {r h j : Nat} (hp : Params r h) :
    shiftedAdjacentLo r h j <= shiftedAdjacentHi r h j := by
  have hh := hp.h_ge_six
  unfold shiftedAdjacentLo shiftedAdjacentHi HLo
  omega

theorem shiftedPairSlice_nonempty {r h m : Nat} (hp : Params r h) :
    shiftedPairSliceLo r h m <= shiftedPairSliceHi r h m := by
  have hh := hp.h_ge_six
  unfold shiftedPairSliceLo shiftedPairSliceHi
  omega

theorem shiftedPairSlice_next_lo_le_hi {r h m : Nat} (hp : Params r h) :
    shiftedPairSliceLo r h (m + 1) <= shiftedPairSliceHi r h m := by
  have hh := hp.h_ge_six
  unfold shiftedPairSliceLo shiftedPairSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem shiftedPairSlice_next_overlap {r h m : Nat} (hp : Params r h) :
    ∃ t : Nat,
      InShiftedPairSlice r h m t ∧ InShiftedPairSlice r h (m + 1) t := by
  refine ⟨shiftedPairSliceLo r h (m + 1), ?_, ?_⟩
  · unfold InShiftedPairSlice InInterval
    constructor
    · unfold shiftedPairSliceLo
      simp [Nat.left_distrib, Nat.right_distrib]
    · exact shiftedPairSlice_next_lo_le_hi (r := r) (h := h) (m := m) hp
  · unfold InShiftedPairSlice InInterval
    exact ⟨by omega, shiftedPairSlice_nonempty (r := r) (h := h) (m := m + 1) hp⟩

/-- A finite chain of overlapping shifted slices covers the interval from the
first left endpoint to the last right endpoint. -/
theorem shiftedPairSlice_chain_cover {r h a n t : Nat} (hp : Params r h)
    (ht :
      InInterval (shiftedPairSliceLo r h a) (shiftedPairSliceHi r h (a + n)) t) :
    ∃ m : Nat, a <= m ∧ m <= a + n ∧ InShiftedPairSlice r h m t := by
  induction n with
  | zero =>
      exact ⟨a, by omega, by omega, ht⟩
  | succ n ih =>
      by_cases htn : t <= shiftedPairSliceHi r h (a + n)
      · rcases ih ⟨ht.1, htn⟩ with ⟨m, hma, hmle, hmem⟩
        exact ⟨m, hma, by omega, hmem⟩
      · have hlo : shiftedPairSliceLo r h ((a + n) + 1) <= t := by
          have hover :=
            shiftedPairSlice_next_lo_le_hi (r := r) (h := h) (m := a + n) hp
          omega
        have hidx : (a + n) + 1 = a + (n + 1) := by omega
        have hhi : t <= shiftedPairSliceHi r h ((a + n) + 1) := by
          simpa [hidx] using ht.2
        exact ⟨(a + n) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

/--
Every target in the sum interval of two closed intervals has a constructive
two-summand witness. This is the non-distinct analogue used for sums of two
different boundary-band intervals.
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

theorem H_shiftedAdjacent_lo_eq_slice_lo {r h i j : Nat} :
    HLo r h i + shiftedAdjacentLo r h j =
      shiftedPairSliceLo r h (i + j) := by
  unfold shiftedAdjacentLo shiftedPairSliceLo HLo
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem H_shiftedAdjacent_hi_eq_slice_hi {r h i j : Nat} (hp : Params r h) :
    HHi r h i + shiftedAdjacentHi r h j =
      shiftedPairSliceHi r h (i + j) := by
  have hh := hp.h_ge_six
  unfold HHi shiftedAdjacentHi shiftedPairSliceHi HLo
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

/--
For any fixed indices `i,j`, the shifted adjacent two-sums cover the slice
indexed by `i+j`.
-/
theorem shifted_adjacent_pair_sum_of_indices {r h i j t : Nat} (hp : Params r h)
    (ht : InShiftedPairSlice r h (i + j) t) :
    ∃ x y : Nat,
      InH r h i x ∧
      InInterval (shiftedAdjacentLo r h j) (shiftedAdjacentHi r h j) y ∧
      x + y = t := by
  have hH : HLo r h i <= HHi r h i := HLo_le_HHi hp
  have hAdj :
      shiftedAdjacentLo r h j <= shiftedAdjacentHi r h j :=
    shiftedAdjacentLo_le_shiftedAdjacentHi (r := r) (h := h) (j := j) hp
  have hlo := H_shiftedAdjacent_lo_eq_slice_lo (r := r) (h := h) (i := i) (j := j)
  have hhi := H_shiftedAdjacent_hi_eq_slice_hi (r := r) (h := h) (i := i) (j := j) hp
  have htSum :
      InInterval (HLo r h i + shiftedAdjacentLo r h j)
        (HHi r h i + shiftedAdjacentHi r h j) t := by
    unfold InShiftedPairSlice at ht
    simpa [hlo, hhi] using ht
  rcases interval_pair_sum hH hAdj htSum with ⟨x, y, hx, hy, hsum⟩
  exact ⟨x, y, hx, hy, hsum⟩

/-- The same coverage with an explicit normalized slice index `m`. -/
theorem shifted_adjacent_pair_sum_of_sum {r h i j m t : Nat} (hp : Params r h)
    (hm : i + j = m) (ht : InShiftedPairSlice r h m t) :
    ∃ x y : Nat,
      InH r h i x ∧
      InInterval (shiftedAdjacentLo r h j) (shiftedAdjacentHi r h j) y ∧
      x + y = t := by
  have ht' : InShiftedPairSlice r h (i + j) t := by
    simpa [hm] using ht
  exact shifted_adjacent_pair_sum_of_indices
    (r := r) (h := h) (i := i) (j := j) hp ht'

/--
For a fixed `m`, choosing `i = 0` and `j = m` gives a constructive witness for
every target in the shifted adjacent slice.
-/
theorem shifted_adjacent_pair_sum_exists {r h m t : Nat} (hp : Params r h)
    (ht : InShiftedPairSlice r h m t) :
    ∃ i j x y : Nat,
      i + j = m ∧
      InH r h i x ∧
      InInterval (shiftedAdjacentLo r h j) (shiftedAdjacentHi r h j) y ∧
      x + y = t := by
  rcases shifted_adjacent_pair_sum_of_sum
      (r := r) (h := h) (i := 0) (j := m) (m := m) hp (by omega) ht with
    ⟨x, y, hx, hy, hsum⟩
  exact ⟨0, m, x, y, by omega, hx, hy, hsum⟩

/-- Left endpoint of the three-`H` sum slice indexed by `m=i+j+k`. -/
def tripleHSliceLo (r h m : Nat) : Nat := 3 * D r h + 2 * m * h

/-- Right endpoint of the three-`H` sum slice indexed by `m=i+j+k`. -/
def tripleHSliceHi (r h m : Nat) : Nat := 3 * D r h + 2 * m * h + 3 * h - 3

/-- Membership in the three-`H` sum slice indexed by `m`. -/
def InTripleHSlice (r h m t : Nat) : Prop :=
  InInterval (tripleHSliceLo r h m) (tripleHSliceHi r h m) t

theorem tripleHSlice_nonempty {r h m : Nat} (hp : Params r h) :
    tripleHSliceLo r h m <= tripleHSliceHi r h m := by
  have hh := hp.h_ge_six
  unfold tripleHSliceLo tripleHSliceHi
  omega

theorem tripleHSlice_next_lo_le_hi {r h m : Nat} (hp : Params r h) :
    tripleHSliceLo r h (m + 1) <= tripleHSliceHi r h m := by
  have hh := hp.h_ge_six
  unfold tripleHSliceLo tripleHSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem tripleHSlice_next_overlap {r h m : Nat} (hp : Params r h) :
    ∃ t : Nat,
      InTripleHSlice r h m t ∧ InTripleHSlice r h (m + 1) t := by
  refine ⟨tripleHSliceLo r h (m + 1), ?_, ?_⟩
  · unfold InTripleHSlice InInterval
    constructor
    · unfold tripleHSliceLo
      simp [Nat.left_distrib, Nat.right_distrib]
    · exact tripleHSlice_next_lo_le_hi (r := r) (h := h) (m := m) hp
  · unfold InTripleHSlice InInterval
    exact ⟨by omega, tripleHSlice_nonempty (r := r) (h := h) (m := m + 1) hp⟩

/--
A finite chain of overlapping three-`H` slices covers the interval from the
first left endpoint to the last right endpoint.
-/
theorem tripleHSlice_chain_cover {r h a n t : Nat} (hp : Params r h)
    (ht :
      InInterval (tripleHSliceLo r h a) (tripleHSliceHi r h (a + n)) t) :
    ∃ m : Nat, a <= m ∧ m <= a + n ∧ InTripleHSlice r h m t := by
  induction n with
  | zero =>
      exact ⟨a, by omega, by omega, ht⟩
  | succ n ih =>
      by_cases htn : t <= tripleHSliceHi r h (a + n)
      · rcases ih ⟨ht.1, htn⟩ with ⟨m, hma, hmle, hmem⟩
        exact ⟨m, hma, by omega, hmem⟩
      · have hlo : tripleHSliceLo r h ((a + n) + 1) <= t := by
          have hover :=
            tripleHSlice_next_lo_le_hi (r := r) (h := h) (m := a + n) hp
          omega
        have hidx : (a + n) + 1 = a + (n + 1) := by omega
        have hhi : t <= tripleHSliceHi r h ((a + n) + 1) := by
          simpa [hidx] using ht.2
        exact ⟨(a + n) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

/--
Every target in the sum interval of three closed intervals has a constructive
three-summand witness. Distinctness is not part of this generic interval
lemma.
-/
theorem interval_triple_sum {L1 U1 L2 U2 L3 U3 t : Nat}
    (h1 : L1 <= U1) (h2 : L2 <= U2) (h3 : L3 <= U3)
    (ht : InInterval (L1 + L2 + L3) (U1 + U2 + U3) t) :
    ∃ u v w : Nat,
      InInterval L1 U1 u ∧
      InInterval L2 U2 v ∧
      InInterval L3 U3 w ∧
      u + v + w = t := by
  have h12 : L1 + L2 <= U1 + U2 := by omega
  have htPair : InInterval ((L1 + L2) + L3) ((U1 + U2) + U3) t := by
    unfold InInterval at *
    constructor <;> omega
  rcases interval_pair_sum h12 h3 htPair with ⟨s, w, hs, hw, hsum_sw⟩
  rcases interval_pair_sum h1 h2 hs with ⟨u, v, hu, hv, hsum_uv⟩
  exact ⟨u, v, w, hu, hv, hw, by omega⟩

theorem H_triple_lo_eq_slice_lo {r h i j k : Nat} :
    HLo r h i + HLo r h j + HLo r h k =
      tripleHSliceLo r h (i + j + k) := by
  unfold HLo tripleHSliceLo
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem H_triple_hi_eq_slice_hi {r h i j k : Nat} (hp : Params r h) :
    HHi r h i + HHi r h j + HHi r h k =
      tripleHSliceHi r h (i + j + k) := by
  have hh := hp.h_ge_six
  unfold HHi HLo tripleHSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

/-- Fixed-index constructive coverage for a three-`H` slice. -/
theorem H_triple_sum_of_indices {r h i j k t : Nat} (hp : Params r h)
    (ht : InTripleHSlice r h (i + j + k) t) :
    ∃ x y z : Nat,
      InH r h i x ∧
      InH r h j y ∧
      InH r h k z ∧
      x + y + z = t := by
  have hI : HLo r h i <= HHi r h i := HLo_le_HHi hp
  have hJ : HLo r h j <= HHi r h j := HLo_le_HHi hp
  have hK : HLo r h k <= HHi r h k := HLo_le_HHi hp
  have hlo := H_triple_lo_eq_slice_lo (r := r) (h := h) (i := i) (j := j) (k := k)
  have hhi := H_triple_hi_eq_slice_hi (r := r) (h := h) (i := i) (j := j) (k := k) hp
  have htSum :
      InInterval (HLo r h i + HLo r h j + HLo r h k)
        (HHi r h i + HHi r h j + HHi r h k) t := by
    unfold InTripleHSlice at ht
    rw [hlo, hhi]
    exact ht
  rcases interval_triple_sum hI hJ hK htSum with ⟨x, y, z, hx, hy, hz, hsum⟩
  exact ⟨x, y, z, hx, hy, hz, hsum⟩

/-- Fixed-index constructive coverage with an explicit normalized slice index. -/
theorem H_triple_sum_of_sum {r h i j k m t : Nat} (hp : Params r h)
    (hm : i + j + k = m) (ht : InTripleHSlice r h m t) :
    ∃ x y z : Nat,
      InH r h i x ∧
      InH r h j y ∧
      InH r h k z ∧
      x + y + z = t := by
  have ht' : InTripleHSlice r h (i + j + k) t := by
    simpa [hm] using ht
  exact H_triple_sum_of_indices
    (r := r) (h := h) (i := i) (j := j) (k := k) hp ht'

end BoundaryRBand
end GreedyThreeSumfree
