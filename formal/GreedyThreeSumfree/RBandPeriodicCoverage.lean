import GreedyThreeSumfree.RBandCoverageAssembly
import GreedyThreeSumfree.RBandPeriodicSafety

namespace GreedyThreeSumfree
namespace RBand

/--
Membership in the translate `I_i + h`, recorded with the original `I_i`
witness.  This is the offset form of an internal periodic gap.
-/
def InIAddH (r h e i t : Nat) : Prop :=
  ∃ v : Nat, InI r h e i v ∧ v + h = t

/-- Interval membership in `I_i+h` gives the corresponding translated witness. -/
theorem inIAddH_of_interval {r h e i t : Nat}
    (ht : InInterval (ILo r h e i + h) (IHi r h e i + h) t) :
    InIAddH r h e i t := by
  let v := t - h
  have hh_le_t : h <= t := by
    exact Nat.le_trans (Nat.le_add_left h (ILo r h e i)) ht.1
  have hvlo : ILo r h e i <= v := by
    dsimp [v]
    exact Nat.le_sub_of_add_le ht.1
  have hvhi : v <= IHi r h e i := by
    dsimp [v]
    rw [Nat.sub_le_iff_le_add]
    exact ht.2
  have hsum : v + h = t := by
    dsimp [v]
    exact Nat.sub_add_cancel hh_le_t
  exact ⟨v, ⟨hvlo, hvhi⟩, hsum⟩

/-- A positive periodic translate of a residue in `V` is a candidate. -/
theorem candidate_of_periodic_residue {r h e q rho : Nat}
    (hq : 1 <= q) (hrho : InV r h e rho) :
    Candidate r h e (q * M r h e + rho) := by
  exact Or.inr ⟨q, hq, ⟨rho, hrho, rfl⟩⟩

/-- Prefix candidates are below every positive periodic translate. -/
theorem prefix_lt_positive_periodic_residue {r h e q p rho : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (hpfx : InPrefix r h e p) (_hrho : InV r h e rho) :
    p < q * M r h e + rho := by
  have hp_lt_M : p < M r h e := prefix_lt_M hp hpfx
  have hM_le_qM : M r h e <= q * M r h e := by
    have hmul : 1 * M r h e <= q * M r h e :=
      Nat.mul_le_mul_right (M r h e) hq
    simpa using hmul
  omega

/--
Explicit internal periodic-gap witness.

For `t = v+h` with `v in I_i`, the target `qM+t` is represented as
`1 + (h-1) + (qM+v)`.  The summands are candidates, ordered increasingly, and
the periodic summand is still below the target.
-/
theorem periodic_internal_gap_candidate_triple_witness {r h e q i t : Nat}
    (hp : Params r h e) (hq : 1 <= q) (hi : i < r)
    (ht : InIAddH r h e i t) :
    ∃ v : Nat,
      InI r h e i v ∧
      v + h = t ∧
      Candidate r h e 1 ∧
      Candidate r h e (h - 1) ∧
      Candidate r h e (q * M r h e + v) ∧
      1 < h - 1 ∧
      h - 1 < q * M r h e + v ∧
      q * M r h e + v < q * M r h e + t ∧
      1 + (h - 1) + (q * M r h e + v) = q * M r h e + t := by
  rcases ht with ⟨v, hvI, hvt⟩
  have hvV : InV r h e v := ⟨i, hi, hvI⟩
  have hper : Candidate r h e (q * M r h e + v) :=
    candidate_of_periodic_residue (r := r) (h := h) (e := e) (q := q) hq hvV
  have hlt_one_h : 1 < h - 1 := by
    have hh := hp.h_ge_six
    omega
  have hlt_h_per : h - 1 < q * M r h e + v :=
    prefix_lt_positive_periodic_residue
      (r := r) (h := h) (e := e) (q := q) (p := h - 1) (rho := v)
      hp hq (prefix_h_sub_one r h e) hvV
  have hv_lt_t : v < t := by
    have hh := hp.h_ge_six
    omega
  have hper_lt_target : q * M r h e + v < q * M r h e + t := by
    exact Nat.add_lt_add_left hv_lt_t (q * M r h e)
  have hsum : 1 + (h - 1) + (q * M r h e + v) = q * M r h e + t := by
    have hh := hp.h_ge_six
    omega
  exact
    ⟨v, hvI, hvt, candidate_one r h e, candidate_h_sub_one r h e, hper,
      hlt_one_h, hlt_h_per, hper_lt_target, hsum⟩

/--
Internal periodic-gap coverage for one regular `r`-band slice.

If `i<r` and the offset `t` lies in `I_i+h`, then `qM+t` is a sum of three
distinct smaller candidates.
-/
theorem periodic_internal_gap_candidate_triple {r h e q i t : Nat}
    (hp : Params r h e) (hq : 1 <= q) (hi : i < r)
    (ht : InInterval (ILo r h e i + h) (IHi r h e i + h) t) :
    CandidateTripleSumFrom r h e (q * M r h e + t) := by
  rcases periodic_internal_gap_candidate_triple_witness
      (r := r) (h := h) (e := e) (q := q) (i := i) (t := t)
      hp hq hi (inIAddH_of_interval (r := r) (h := h) (e := e) (i := i) ht) with
    ⟨v, _hvI, _hvt, h1, hh1, hper, hlt_one_h, hlt_h_per, hper_lt_target, hsum⟩
  exact ⟨1, h - 1, q * M r h e + v, h1, hh1, hper,
    hlt_one_h, hlt_h_per, hper_lt_target, hsum⟩

/-- Left endpoint for the shifted `V + {1,h-1} + U` slice. -/
def shiftedVUSliceLo (r h e m : Nat) : Nat :=
  shiftedPairSliceLo r h e m - 2

/-- Right endpoint for the shifted `V + {1,h-1} + U` slice. -/
def shiftedVUSliceHi (r h e m : Nat) : Nat :=
  shiftedPairSliceHi r h e m - 2

/-- Membership in one shifted `V + {1,h-1} + U` slice. -/
def InShiftedVUSlice (r h e m t : Nat) : Prop :=
  InInterval (shiftedVUSliceLo r h e m) (shiftedVUSliceHi r h e m) t

theorem shiftedPairSlice_of_shiftedVUSlice_add_two {r h e m t : Nat}
    (hp : Params r h e) (ht : InShiftedVUSlice r h e m t) :
    InShiftedPairSlice r h e m (t + 2) := by
  have hlo2 : 2 <= shiftedPairSliceLo r h e m := by
    unfold shiftedPairSliceLo
    omega
  have hhi2 : 2 <= shiftedPairSliceHi r h e m := by
    have hD := D_ge_three (r := r) (h := h) (e := e) hp
    have hh := hp.h_ge_six
    unfold shiftedPairSliceHi
    omega
  unfold InShiftedVUSlice InShiftedPairSlice InInterval at *
  unfold shiftedVUSliceLo shiftedVUSliceHi at ht
  constructor <;> omega

theorem shiftedVUSlice_of_shiftedPairSlice_add_two {r h e m t : Nat}
    (hp : Params r h e) (ht : InShiftedPairSlice r h e m (t + 2)) :
    InShiftedVUSlice r h e m t := by
  have hlo2 : 2 <= shiftedPairSliceLo r h e m := by
    unfold shiftedPairSliceLo
    omega
  have hhi2 : 2 <= shiftedPairSliceHi r h e m := by
    have hD := D_ge_three (r := r) (h := h) (e := e) hp
    have hh := hp.h_ge_six
    unfold shiftedPairSliceHi
    omega
  unfold InShiftedVUSlice InShiftedPairSlice InInterval at *
  unfold shiftedVUSliceLo shiftedVUSliceHi
  constructor <;> omega

/--
Slice-level shifted `V + {1,h-1} + U` coverage.

This reuses the existing shifted-pair witness for `t+2`, then moves the first
`H_i` witness down by two into `I_i`.
-/
theorem shifted_VU_slice_candidate_triple {r h e q m t : Nat}
    (hp : Params r h e) (hq : 1 <= q) (hm : m <= 2 * r - 2)
    (ht : InShiftedVUSlice r h e m t) :
    CandidateTripleSumFrom r h e (q * M r h e + t) := by
  have htPair : InShiftedPairSlice r h e m (t + 2) :=
    shiftedPairSlice_of_shiftedVUSlice_add_two
      (r := r) (h := h) (e := e) (m := m) (t := t) hp ht
  rcases shifted_pair_slice_prefix_pair_inPrefix_witness
      (r := r) (h := h) (e := e) (m := m) (t := t + 2) hp hm htPair with
    ⟨eps, i, j, x, u, heps, hi, hj, _hij, hxH, huH, hepsP, _hxP, huP, hsumPair⟩
  let v := x - 2
  have hvI : InI r h e i v := by
    dsimp [v]
    exact sub_two_mem_I_of_mem_H (r := r) (h := h) (e := e) (i := i) (x := x) hp hxH
  have hvV : InV r h e v := ⟨i, hi, hvI⟩
  have hper : Candidate r h e (q * M r h e + v) :=
    candidate_of_periodic_residue (r := r) (h := h) (e := e) (q := q) hq hvV
  have huCand : Candidate r h e u := candidate_of_prefix huP
  have hepsCand : Candidate r h e eps := candidate_of_prefix hepsP
  have hx_ge_two : 2 <= x := by
    have hHlo := HLo_ge_three (r := r) (h := h) (e := e) (i := i) hp
    exact Nat.le_trans (by omega : 2 <= HLo r h e i) hxH.1
  have hx_sub : v + 2 = x := by
    dsimp [v]
    exact Nat.sub_add_cancel hx_ge_two
  have hsumPair' : eps + (v + 2) + u = t + 2 := by
    simpa [hx_sub] using hsumPair
  have hsumOffset : eps + v + u = t := by
    omega
  have hu_ge_h_add_one : h + 1 <= u := by
    have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
    unfold InH InInterval HLo at huH
    omega
  have heps_lt_u : eps < u := by
    rcases heps with rfl | rfl
    · have hh := hp.h_ge_six
      omega
    · have hh := hp.h_ge_six
      omega
  have hu_lt_per : u < q * M r h e + v :=
    prefix_lt_positive_periodic_residue
      (r := r) (h := h) (e := e) (q := q) (p := u) (rho := v)
      hp hq huP hvV
  have heps_pos : 1 <= eps := by
    rcases heps with rfl | rfl
    · omega
    · have hh := hp.h_ge_six
      omega
  have hu_pos : 1 <= u := by omega
  have hv_lt_t : v < t := by omega
  have hper_lt_target : q * M r h e + v < q * M r h e + t := by
    exact Nat.add_lt_add_left hv_lt_t (q * M r h e)
  have hsumTarget : eps + u + (q * M r h e + v) = q * M r h e + t := by
    omega
  exact
    ⟨eps, u, q * M r h e + v, hepsCand, huCand, hper,
      heps_lt_u, hu_lt_per, hper_lt_target, hsumTarget⟩

/--
The chained shifted `V + {1,h-1} + U` slices cover the corresponding global
offset interval.
-/
theorem shiftedVUSlice_chain_cover_bounded {r h e t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (shiftedVUSliceLo r h e 0)
        (shiftedVUSliceHi r h e (2 * r - 2)) t) :
    ∃ m : Nat, m <= 2 * r - 2 ∧ InShiftedVUSlice r h e m t := by
  have hlo2 : 2 <= shiftedPairSliceLo r h e 0 := by
    unfold shiftedPairSliceLo
    omega
  have hhi2 : 2 <= shiftedPairSliceHi r h e (2 * r - 2) := by
    have hD := D_ge_three (r := r) (h := h) (e := e) hp
    have hh := hp.h_ge_six
    unfold shiftedPairSliceHi
    omega
  have htPairRaw :
      InInterval (shiftedPairSliceLo r h e 0)
        (shiftedPairSliceHi r h e (2 * r - 2)) (t + 2) := by
    unfold InInterval at *
    unfold shiftedVUSliceLo shiftedVUSliceHi at ht
    constructor <;> omega
  have htPair :
      InInterval (2 * D r h e + 2)
        (2 * D r h e + (4 * r - 1) * h - 4) (t + 2) := by
    have hlo := shiftedPairSlice_global_lo_eq r h e
    have hhi := shiftedPairSlice_global_hi_eq (r := r) (h := h) (e := e) hp
    rw [← hlo, ← hhi]
    exact htPairRaw
  rcases shiftedPairSlice_chain_cover_bounded
      (r := r) (h := h) (e := e) (t := t + 2) hp htPair with
    ⟨m, hm, hmPair⟩
  exact ⟨m, hm,
    shiftedVUSlice_of_shiftedPairSlice_add_two
      (r := r) (h := h) (e := e) (m := m) (t := t) hp hmPair⟩

/--
Candidate-triple coverage for the full shifted `V + {1,h-1} + U` chain.
-/
theorem shifted_VU_chain_candidate_triple {r h e q t : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (ht :
      InInterval (shiftedVUSliceLo r h e 0)
        (shiftedVUSliceHi r h e (2 * r - 2)) t) :
    CandidateTripleSumFrom r h e (q * M r h e + t) := by
  rcases shiftedVUSlice_chain_cover_bounded
      (r := r) (h := h) (e := e) (t := t) hp ht with
    ⟨m, hm, hmem⟩
  exact shifted_VU_slice_candidate_triple
    (r := r) (h := h) (e := e) (q := q) (m := m) (t := t) hp hq hm hmem

end RBand
end GreedyThreeSumfree
