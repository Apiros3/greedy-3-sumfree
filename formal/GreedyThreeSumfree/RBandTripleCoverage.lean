import GreedyThreeSumfree.RBandCoverage

namespace GreedyThreeSumfree
namespace RBand

/--
Bounded index selection for three regular-band intervals.

If `m` lies in the possible sum-index range `0..3r-3`, then it can be
written as `i+j+k` with all three indices in the regular `r`-band range.
-/
theorem bounded_triple_indices {r m : Nat} (hr : 1 <= r) (hm : m <= 3 * r - 3) :
    ∃ i j k : Nat, i < r ∧ j < r ∧ k < r ∧ i + j + k = m := by
  by_cases hm_pair : m <= 2 * r - 2
  · rcases bounded_pair_indices (r := r) (m := m) hr hm_pair with
      ⟨i, j, hi, hj, hij⟩
    exact ⟨i, j, 0, hi, hj, by omega, by omega⟩
  · have hm' : m - (r - 1) <= 2 * r - 2 := by omega
    rcases bounded_pair_indices (r := r) (m := m - (r - 1)) hr hm' with
      ⟨i, j, hi, hj, hij⟩
    exact ⟨i, j, r - 1, hi, hj, by omega, by omega⟩

/-- Left endpoint of the three-`H` sum slice indexed by `m=i+j+k`. -/
def tripleHSliceLo (r h e m : Nat) : Nat := 3 * D r h e + 2 * m * h

/-- Right endpoint of the three-`H` sum slice indexed by `m=i+j+k`. -/
def tripleHSliceHi (r h e m : Nat) : Nat := 3 * D r h e + 2 * m * h + 3 * h - 3

/-- Membership in the three-`H` sum slice indexed by `m`. -/
def InTripleHSlice (r h e m t : Nat) : Prop :=
  InInterval (tripleHSliceLo r h e m) (tripleHSliceHi r h e m) t

theorem tripleHSlice_nonempty {r h e m : Nat} (hp : Params r h e) :
    tripleHSliceLo r h e m <= tripleHSliceHi r h e m := by
  have hh := hp.h_ge_six
  unfold tripleHSliceLo tripleHSliceHi
  omega

theorem tripleHSlice_next_lo_le_hi {r h e m : Nat} (hp : Params r h e) :
    tripleHSliceLo r h e (m + 1) <= tripleHSliceHi r h e m := by
  have hh := hp.h_ge_six
  unfold tripleHSliceLo tripleHSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem tripleHSlice_next_overlap {r h e m : Nat} (hp : Params r h e) :
    ∃ t : Nat,
      InTripleHSlice r h e m t ∧ InTripleHSlice r h e (m + 1) t := by
  refine ⟨tripleHSliceLo r h e (m + 1), ?_, ?_⟩
  · unfold InTripleHSlice InInterval
    constructor
    · unfold tripleHSliceLo
      simp [Nat.left_distrib, Nat.right_distrib]
    · exact tripleHSlice_next_lo_le_hi (r := r) (h := h) (e := e) (m := m) hp
  · unfold InTripleHSlice InInterval
    exact ⟨by omega, tripleHSlice_nonempty (r := r) (h := h) (e := e) (m := m + 1) hp⟩

/--
A finite chain of overlapping three-`H` slices covers the interval from the
first left endpoint to the last right endpoint.
-/
theorem tripleHSlice_chain_cover {r h e a n t : Nat} (hp : Params r h e)
    (ht :
      InInterval (tripleHSliceLo r h e a) (tripleHSliceHi r h e (a + n)) t) :
    ∃ m : Nat, a <= m ∧ m <= a + n ∧ InTripleHSlice r h e m t := by
  induction n with
  | zero =>
      exact ⟨a, by omega, by omega, ht⟩
  | succ n ih =>
      by_cases htn : t <= tripleHSliceHi r h e (a + n)
      · rcases ih ⟨ht.1, htn⟩ with ⟨m, hma, hmle, hmem⟩
        exact ⟨m, hma, by omega, hmem⟩
      · have hlo : tripleHSliceLo r h e ((a + n) + 1) <= t := by
          have hover :=
            tripleHSlice_next_lo_le_hi (r := r) (h := h) (e := e) (m := a + n) hp
          omega
        have hidx : (a + n) + 1 = a + (n + 1) := by omega
        have hhi : t <= tripleHSliceHi r h e ((a + n) + 1) := by
          simpa [hidx] using ht.2
        exact ⟨(a + n) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

/--
Every target in the sum interval of three closed intervals has a constructive
three-summand witness.  Distinctness is not part of this generic interval
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

theorem H_triple_lo_eq_slice_lo {r h e i j k : Nat} :
    HLo r h e i + HLo r h e j + HLo r h e k =
      tripleHSliceLo r h e (i + j + k) := by
  unfold HLo tripleHSliceLo
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem H_triple_hi_eq_slice_hi {r h e i j k : Nat} (hp : Params r h e) :
    HHi r h e i + HHi r h e j + HHi r h e k =
      tripleHSliceHi r h e (i + j + k) := by
  have hh := hp.h_ge_six
  unfold HHi HLo tripleHSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

/-- Fixed-index constructive coverage for a three-`H` slice. -/
theorem H_triple_sum_of_indices {r h e i j k t : Nat} (hp : Params r h e)
    (ht : InTripleHSlice r h e (i + j + k) t) :
    ∃ x y z : Nat,
      InH r h e i x ∧
      InH r h e j y ∧
      InH r h e k z ∧
      x + y + z = t := by
  have hI : HLo r h e i <= HHi r h e i := HLo_le_HHi hp
  have hJ : HLo r h e j <= HHi r h e j := HLo_le_HHi hp
  have hK : HLo r h e k <= HHi r h e k := HLo_le_HHi hp
  have hlo := H_triple_lo_eq_slice_lo (r := r) (h := h) (e := e) (i := i) (j := j) (k := k)
  have hhi := H_triple_hi_eq_slice_hi (r := r) (h := h) (e := e) (i := i) (j := j) (k := k) hp
  have htSum :
      InInterval (HLo r h e i + HLo r h e j + HLo r h e k)
        (HHi r h e i + HHi r h e j + HHi r h e k) t := by
    unfold InTripleHSlice at ht
    rw [hlo, hhi]
    exact ht
  rcases interval_triple_sum hI hJ hK htSum with ⟨x, y, z, hx, hy, hz, hsum⟩
  exact ⟨x, y, z, hx, hy, hz, hsum⟩

/-- Fixed-index constructive coverage with an explicit normalized slice index. -/
theorem H_triple_sum_of_sum {r h e i j k m t : Nat} (hp : Params r h e)
    (hm : i + j + k = m) (ht : InTripleHSlice r h e m t) :
    ∃ x y z : Nat,
      InH r h e i x ∧
      InH r h e j y ∧
      InH r h e k z ∧
      x + y + z = t := by
  have ht' : InTripleHSlice r h e (i + j + k) t := by
    simpa [hm] using ht
  exact H_triple_sum_of_indices
    (r := r) (h := h) (e := e) (i := i) (j := j) (k := k) hp ht'

/--
Bounded three-`H` coverage for one slice: every target in a feasible slice has
a witness from three bounded regular-band intervals.
-/
theorem H_triple_sum_exists_bounded {r h e m t : Nat} (hp : Params r h e)
    (hm : m <= 3 * r - 3) (ht : InTripleHSlice r h e m t) :
    ∃ i j k x y z : Nat,
      i < r ∧
      j < r ∧
      k < r ∧
      i + j + k = m ∧
      InH r h e i x ∧
      InH r h e j y ∧
      InH r h e k z ∧
      x + y + z = t := by
  rcases bounded_triple_indices (r := r) (m := m) hp.r_pos hm with
    ⟨i, j, k, hi, hj, hk, hijk⟩
  rcases H_triple_sum_of_sum
      (r := r) (h := h) (e := e) (i := i) (j := j) (k := k) (m := m) hp hijk ht with
    ⟨x, y, z, hx, hy, hz, hsum⟩
  exact ⟨i, j, k, x, y, z, hi, hj, hk, hijk, hx, hy, hz, hsum⟩

/-- The bounded slice witness repackaged as a witness from the union `U`. -/
theorem tripleHSlice_U_witness {r h e m t : Nat} (hp : Params r h e)
    (hm : m <= 3 * r - 3) (ht : InTripleHSlice r h e m t) :
    ∃ x y z : Nat,
      InU r h e x ∧ InU r h e y ∧ InU r h e z ∧ x + y + z = t := by
  rcases H_triple_sum_exists_bounded
      (r := r) (h := h) (e := e) (m := m) (t := t) hp hm ht with
    ⟨i, j, k, x, y, z, hi, hj, hk, _hijk, hx, hy, hz, hsum⟩
  exact ⟨x, y, z, ⟨i, hi, hx⟩, ⟨j, hj, hy⟩, ⟨k, hk, hz⟩, hsum⟩

/--
The chain of all feasible three-`H` slices covers the full non-distinct
three-`U` sum range.
-/
theorem tripleHSlice_chain_cover_bounded {r h e t : Nat} (hp : Params r h e)
    (ht :
      InInterval (tripleHSliceLo r h e 0)
        (tripleHSliceHi r h e (3 * r - 3)) t) :
    ∃ m : Nat, m <= 3 * r - 3 ∧ InTripleHSlice r h e m t := by
  have ht' :
      InInterval (tripleHSliceLo r h e 0)
        (tripleHSliceHi r h e (0 + (3 * r - 3))) t := by
    simpa using ht
  rcases tripleHSlice_chain_cover
      (r := r) (h := h) (e := e) (a := 0) (n := 3 * r - 3) (t := t) hp ht' with
    ⟨m, _hmlo, hmhi, hmem⟩
  exact ⟨m, by omega, hmem⟩

/--
Every target in the full non-distinct three-`U` sum range has a three-`U`
witness.
-/
theorem tripleHSlice_chain_U_witness {r h e t : Nat} (hp : Params r h e)
    (ht :
      InInterval (tripleHSliceLo r h e 0)
        (tripleHSliceHi r h e (3 * r - 3)) t) :
    ∃ x y z : Nat,
      InU r h e x ∧ InU r h e y ∧ InU r h e z ∧ x + y + z = t := by
  rcases tripleHSlice_chain_cover_bounded
      (r := r) (h := h) (e := e) (t := t) hp ht with
    ⟨m, hm, hmem⟩
  exact tripleHSlice_U_witness (r := r) (h := h) (e := e) (m := m) hp hm hmem

theorem tripleHSlice_global_lo_eq (r h e : Nat) :
    tripleHSliceLo r h e 0 = 3 * D r h e := by
  unfold tripleHSliceLo
  omega

theorem tripleHSlice_global_hi_eq {r h e : Nat} (hp : Params r h e) :
    tripleHSliceHi r h e (3 * r - 3) =
      3 * D r h e + (6 * r - 3) * h - 3 := by
  have hr := hp.r_pos
  have hcoef : 2 * (3 * r - 3) + 3 = 6 * r - 3 := by omega
  have hprod : 2 * (3 * r - 3) * h + 3 * h = (6 * r - 3) * h := by
    rw [← Nat.add_mul, hcoef]
  unfold tripleHSliceHi
  omega

theorem HHi_lt_HLo_of_lt {r h e i j : Nat} (hp : Params r h e) (hij : i < j) :
    HHi r h e i < HLo r h e j := by
  have hh := hp.h_ge_six
  have hij_le : i + 1 <= j := by omega
  have hcoef : 2 * (i + 1) <= 2 * j := Nat.mul_le_mul_left 2 hij_le
  have hprod : 2 * (i + 1) * h <= 2 * j * h :=
    Nat.mul_le_mul_right h hcoef
  have hprod_eq : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
    simp [Nat.left_distrib, Nat.right_distrib]
  rw [hprod_eq] at hprod
  have hhi_bound : HHi r h e i < D r h e + 2 * i * h + 2 * h := by
    unfold HHi HLo
    omega
  have hlo_bound : D r h e + 2 * i * h + 2 * h <= HLo r h e j := by
    unfold HLo
    omega
  exact Nat.lt_of_lt_of_le hhi_bound hlo_bound

/--
For strictly increasing interval indices, the fixed-index three-`H` witness is
automatically ordered and therefore distinct.
-/
theorem H_triple_sum_distinct_of_strict_indices {r h e i j k t : Nat}
    (hp : Params r h e) (hij : i < j) (hjk : j < k)
    (ht : InTripleHSlice r h e (i + j + k) t) :
    ∃ x y z : Nat,
      InH r h e i x ∧
      InH r h e j y ∧
      InH r h e k z ∧
      x < y ∧ y < z ∧ x + y + z = t := by
  rcases H_triple_sum_of_indices
      (r := r) (h := h) (e := e) (i := i) (j := j) (k := k) hp ht with
    ⟨x, y, z, hx, hy, hz, hsum⟩
  have hxy_gap := HHi_lt_HLo_of_lt (r := r) (h := h) (e := e) hp hij
  have hyz_gap := HHi_lt_HLo_of_lt (r := r) (h := h) (e := e) hp hjk
  have hxy : x < y := by
    exact Nat.lt_of_le_of_lt hx.2 (Nat.lt_of_lt_of_le hxy_gap hy.1)
  have hyz : y < z := by
    exact Nat.lt_of_le_of_lt hy.2 (Nat.lt_of_lt_of_le hyz_gap hz.1)
  exact ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩

/--
Same-interval distinct three-sum coverage for the interior of one `H_i`.
This proves the standard endpoint trimming `[3L+3, 3U-3]` for `L=HLo_i`,
`U=HHi_i`.
-/
theorem H_triple_sum_distinct_same_index {r h e i t : Nat} (hp : Params r h e)
    (ht : InInterval (3 * HLo r h e i + 3) (3 * HHi r h e i - 3) t) :
    ∃ x y z : Nat,
      InH r h e i x ∧
      InH r h e i y ∧
      InH r h e i z ∧
      x < y ∧ y < z ∧ x + y + z = t := by
  have hh := hp.h_ge_six
  have hwidth : HLo r h e i + 2 <= HHi r h e i := by
    unfold HHi
    omega
  have htNat : NatInterval (3 * HLo r h e i + 3) (3 * HHi r h e i - 3) t := by
    simpa [NatInterval, InInterval] using ht
  rcases interval_triple_sum_distinct hwidth htNat with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  refine ⟨x, y, z, ?_, ?_, ?_, hxy, hyz, hsum⟩
  · simpa [InH, NatInterval, InInterval] using hx
  · simpa [InH, NatInterval, InInterval] using hy
  · simpa [InH, NatInterval, InInterval] using hz

end RBand
end GreedyThreeSumfree
