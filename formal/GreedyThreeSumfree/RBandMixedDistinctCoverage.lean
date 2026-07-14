import GreedyThreeSumfree.RBandCoverageAssembly

namespace GreedyThreeSumfree
namespace RBand

theorem HLo_lt_HHi {r h e i : Nat} (hp : Params r h e) :
    HLo r h e i < HHi r h e i := by
  have hh := hp.h_ge_six
  unfold HHi
  omega

/--
Same-`H_i` two-sum coverage with ordered distinct witnesses.

The endpoint trim is the usual distinct-pair range
`[2 * HLo_i + 1, 2 * HHi_i - 1]`.
-/
theorem H_pair_sum_distinct_same_index {r h e i t : Nat} (hp : Params r h e)
    (ht : InInterval (2 * HLo r h e i + 1) (2 * HHi r h e i - 1) t) :
    ∃ x y : Nat,
      InH r h e i x ∧
      InH r h e i y ∧
      x < y ∧
      x + y = t := by
  have hLU : HLo r h e i < HHi r h e i := HLo_lt_HHi hp
  have htNat :
      NatInterval (2 * HLo r h e i + 1) (2 * HHi r h e i - 1) t := by
    simpa [NatInterval, InInterval] using ht
  rcases interval_pair_sum_distinct hLU htNat with
    ⟨x, y, hx, hy, hxy, hsum⟩
  refine ⟨x, y, ?_, ?_, hxy, hsum⟩
  · simpa [InH, NatInterval, InInterval] using hx
  · simpa [InH, NatInterval, InInterval] using hy

theorem H_pair_distinct_sum_interval_nonempty {r h e i : Nat} (hp : Params r h e) :
    2 * HLo r h e i + 1 <= 2 * HHi r h e i - 1 := by
  have hh := hp.h_ge_six
  unfold HHi
  omega

/--
Mixed-index three-sum coverage for the case `{i,i,j}` with `i < j`.

The two witnesses from `H_i` are supplied by `interval_pair_sum_distinct`;
the final witness lies in `H_j`.  The range is exactly
`(H_i + H_i)_distinct + H_j`.
-/
theorem H_triple_sum_distinct_two_left_indices {r h e i j t : Nat}
    (hp : Params r h e) (hij : i < j)
    (ht :
      InInterval (2 * HLo r h e i + 1 + HLo r h e j)
        (2 * HHi r h e i - 1 + HHi r h e j) t) :
    ∃ x y z : Nat,
      InH r h e i x ∧
      InH r h e i y ∧
      InH r h e j z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hPair : 2 * HLo r h e i + 1 <= 2 * HHi r h e i - 1 :=
    H_pair_distinct_sum_interval_nonempty (r := r) (h := h) (e := e) (i := i) hp
  have hJ : HLo r h e j <= HHi r h e j := HLo_le_HHi hp
  rcases interval_pair_sum hPair hJ ht with ⟨s, z, hs, hz, hsum_sz⟩
  rcases H_pair_sum_distinct_same_index
      (r := r) (h := h) (e := e) (i := i) (t := s) hp hs with
    ⟨x, y, hx, hy, hxy, hsum_xy⟩
  have hgap := HHi_lt_HLo_of_lt (r := r) (h := h) (e := e) hp hij
  have hyz : y < z := by
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hy.2 hgap) hz.1
  exact ⟨x, y, z, hx, hy, hz, hxy, hyz, by omega⟩

/--
Mixed-index three-sum coverage for the case `{i,j,j}` with `i < j`.

This is the symmetric endpoint-trimmed range
`H_i + (H_j + H_j)_distinct`.
-/
theorem H_triple_sum_distinct_two_right_indices {r h e i j t : Nat}
    (hp : Params r h e) (hij : i < j)
    (ht :
      InInterval (HLo r h e i + (2 * HLo r h e j + 1))
        (HHi r h e i + (2 * HHi r h e j - 1)) t) :
    ∃ x y z : Nat,
      InH r h e i x ∧
      InH r h e j y ∧
      InH r h e j z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hI : HLo r h e i <= HHi r h e i := HLo_le_HHi hp
  have hPair : 2 * HLo r h e j + 1 <= 2 * HHi r h e j - 1 :=
    H_pair_distinct_sum_interval_nonempty (r := r) (h := h) (e := e) (i := j) hp
  rcases interval_pair_sum hI hPair ht with ⟨x, s, hx, hs, hsum_xs⟩
  rcases H_pair_sum_distinct_same_index
      (r := r) (h := h) (e := e) (i := j) (t := s) hp hs with
    ⟨y, z, hy, hz, hyz, hsum_yz⟩
  have hgap := HHi_lt_HLo_of_lt (r := r) (h := h) (e := e) hp hij
  have hxy : x < y := by
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hx.2 hgap) hy.1
  exact ⟨x, y, z, hx, hy, hz, hxy, hyz, by omega⟩

/-- Bounded `U` form of `H_triple_sum_distinct_two_left_indices`. -/
theorem H_triple_sum_distinct_two_left_inU {r h e i j t : Nat}
    (hp : Params r h e) (hi : i < r) (hj : j < r) (hij : i < j)
    (ht :
      InInterval (2 * HLo r h e i + 1 + HLo r h e j)
        (2 * HHi r h e i - 1 + HHi r h e j) t) :
    ∃ x y z : Nat,
      InU r h e x ∧
      InU r h e y ∧
      InU r h e z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  rcases H_triple_sum_distinct_two_left_indices
      (r := r) (h := h) (e := e) (i := i) (j := j) (t := t) hp hij ht with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  exact
    ⟨x, y, z, ⟨i, hi, hx⟩, ⟨i, hi, hy⟩, ⟨j, hj, hz⟩, hxy, hyz, hsum⟩

/-- Bounded `U` form of `H_triple_sum_distinct_two_right_indices`. -/
theorem H_triple_sum_distinct_two_right_inU {r h e i j t : Nat}
    (hp : Params r h e) (hi : i < r) (hj : j < r) (hij : i < j)
    (ht :
      InInterval (HLo r h e i + (2 * HLo r h e j + 1))
        (HHi r h e i + (2 * HHi r h e j - 1)) t) :
    ∃ x y z : Nat,
      InU r h e x ∧
      InU r h e y ∧
      InU r h e z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  rcases H_triple_sum_distinct_two_right_indices
      (r := r) (h := h) (e := e) (i := i) (j := j) (t := t) hp hij ht with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  exact
    ⟨x, y, z, ⟨i, hi, hx⟩, ⟨j, hj, hy⟩, ⟨j, hj, hz⟩, hxy, hyz, hsum⟩

/--
Trimmed mixed slice `{i,i,j}` as a distinct three-`U` witness.

This is the piece of the three-`U` chain where exactly two interval indices
coincide; the full slice endpoints are trimmed by one on each side.
-/
theorem tripleHSlice_distinct_two_left_inU {r h e i j t : Nat}
    (hp : Params r h e) (hi : i < r) (hj : j < r) (hij : i < j)
    (ht :
      InInterval (tripleHSliceLo r h e (i + i + j) + 1)
        (tripleHSliceHi r h e (i + i + j) - 1) t) :
    ∃ x y z : Nat,
      InU r h e x ∧
      InU r h e y ∧
      InU r h e z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hlo :
      2 * HLo r h e i + 1 + HLo r h e j =
        tripleHSliceLo r h e (i + i + j) + 1 := by
    unfold HLo tripleHSliceLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hhi :
      2 * HHi r h e i - 1 + HHi r h e j =
        tripleHSliceHi r h e (i + i + j) - 1 := by
    have hh := hp.h_ge_six
    unfold HHi HLo tripleHSliceHi
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have htMixed :
      InInterval (2 * HLo r h e i + 1 + HLo r h e j)
        (2 * HHi r h e i - 1 + HHi r h e j) t := by
    rw [hlo, hhi]
    exact ht
  exact H_triple_sum_distinct_two_left_inU
    (r := r) (h := h) (e := e) (i := i) (j := j) (t := t) hp hi hj hij htMixed

/--
Trimmed mixed slice `{i,j,j}` as a distinct three-`U` witness.

This is the companion mixed case where the repeated interval is the upper
index.
-/
theorem tripleHSlice_distinct_two_right_inU {r h e i j t : Nat}
    (hp : Params r h e) (hi : i < r) (hj : j < r) (hij : i < j)
    (ht :
      InInterval (tripleHSliceLo r h e (i + j + j) + 1)
        (tripleHSliceHi r h e (i + j + j) - 1) t) :
    ∃ x y z : Nat,
      InU r h e x ∧
      InU r h e y ∧
      InU r h e z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hlo :
      HLo r h e i + (2 * HLo r h e j + 1) =
        tripleHSliceLo r h e (i + j + j) + 1 := by
    unfold HLo tripleHSliceLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hhi :
      HHi r h e i + (2 * HHi r h e j - 1) =
        tripleHSliceHi r h e (i + j + j) - 1 := by
    have hh := hp.h_ge_six
    unfold HHi HLo tripleHSliceHi
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have htMixed :
      InInterval (HLo r h e i + (2 * HLo r h e j + 1))
        (HHi r h e i + (2 * HHi r h e j - 1)) t := by
    rw [hlo, hhi]
    exact ht
  exact H_triple_sum_distinct_two_right_inU
    (r := r) (h := h) (e := e) (i := i) (j := j) (t := t) hp hi hj hij htMixed

end RBand
end GreedyThreeSumfree
