import GreedyThreeSumfree.RBandPeriodicSafety
import GreedyThreeSumfree.RBandCoverageAssembly

namespace GreedyThreeSumfree
namespace RBand

theorem candidate_lt_M_prefix {r h e n : Nat} (_hp : Params r h e)
    (hn : Candidate r h e n) (hnlt : n < M r h e) :
    InPrefix r h e n := by
  rcases hn with hpfx | hblock
  · exact hpfx
  · rcases hblock with ⟨q, hq, hnblock⟩
    have hMle := periodic_block_ge_M (r := r) (h := h) (e := e)
      (q := q) (n := n) hq hnblock
    omega

theorem inU_lower {r h e n : Nat} (_hp : Params r h e)
    (hn : InU r h e n) :
    D r h e <= n := by
  rcases hn with ⟨i, _hi, hnH⟩
  unfold InH InInterval HLo at hnH
  omega

theorem inU_upper_last {r h e n : Nat} (hp : Params r h e)
    (hn : InU r h e n) :
    n <= HHi r h e (r - 1) := by
  rcases hn with ⟨i, hi, hnH⟩
  have hlast : i <= r - 1 := by
    have hr := hp.r_pos
    omega
  have hmono := HHi_mono_index (r := r) (h := h) (e := e) hlast
  exact Nat.le_trans hnH.2 hmono

theorem HHi_last_lt_two_D_add_one {r h e : Nat} (hp : Params r h e) :
    HHi r h e (r - 1) < 2 * D r h e + 1 := by
  have hr := hp.r_pos
  have he := hp.e_pos
  have hcoef : 2 * (r - 1) + 1 = 2 * r - 1 := by omega
  have htop_eq : HHi r h e (r - 1) = D r h e + (2 * r - 1) * h - 1 := by
    unfold HHi HLo
    rw [← hcoef, Nat.add_mul, Nat.one_mul]
    omega
  rw [htop_eq]
  unfold D
  omega

theorem inH_add_h_not_inU {r h e i n : Nat} (hp : Params r h e)
    (_hi : i < r) (hn : InH r h e i n) :
    ¬ InU r h e (n + h) := by
  intro hU
  rcases hU with ⟨j, hj, hjH⟩
  by_cases hij : i < j
  · have hgap := HHi_lt_HLo_of_lt (r := r) (h := h) (e := e) hp hij
    have hn_hi : n <= HHi r h e i := hn.2
    have hnh_lt : n + h < HLo r h e j := by
      have hh := hp.h_ge_six
      have hij_le : i + 1 <= j := by omega
      have hcoef : 2 * (i + 1) <= 2 * j := Nat.mul_le_mul_left 2 hij_le
      have hprod : 2 * (i + 1) * h <= 2 * j * h :=
        Nat.mul_le_mul_right h hcoef
      have hprod_eq : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
        simp [Nat.left_distrib, Nat.right_distrib]
      rw [hprod_eq] at hprod
      unfold InH InInterval HHi HLo at hn
      unfold HLo
      omega
    exact (Nat.not_lt_of_ge hjH.1) hnh_lt
  · have hji : j <= i := by omega
    have hcoef : 2 * j + 1 <= 2 * i + 1 := by omega
    have hprod : (2 * j + 1) * h <= (2 * i + 1) * h :=
      Nat.mul_le_mul_right h hcoef
    rw [Nat.add_mul, Nat.one_mul] at hprod
    rw [Nat.add_mul, Nat.one_mul] at hprod
    have hj_hi_le : HHi r h e j <= HHi r h e i := by
      unfold HHi HLo
      omega
    have hnh_gt : HHi r h e i < n + h := by
      have hh := hp.h_ge_six
      have hn_lo : HLo r h e i <= n := hn.1
      unfold HHi
      omega
    exact (Nat.not_lt_of_ge (Nat.le_trans hjH.2 hj_hi_le)) hnh_gt

theorem inU_add_h_not_inU {r h e n : Nat} (hp : Params r h e)
    (hn : InU r h e n) :
    ¬ InU r h e (n + h) := by
  rcases hn with ⟨i, hi, hnH⟩
  exact inH_add_h_not_inU (r := r) (h := h) (e := e) (i := i) (n := n)
    hp hi hnH

theorem prefix_gt_h_sub_one_inU {r h e n : Nat} (hp : Params r h e)
    (hn : InPrefix r h e n) (hgt : h - 1 < n) :
    InU r h e n := by
  unfold InPrefix at hn
  rcases hn with rfl | rfl | hU
  · have hh := hp.h_ge_six
    omega
  · omega
  · exact hU

theorem prefix_triple_sum_not_inU {r h e target x y z : Nat}
    (hp : Params r h e)
    (htU : InU r h e target)
    (hx : InPrefix r h e x) (hy : InPrefix r h e y) (hz : InPrefix r h e z)
    (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = target) :
    False := by
  have htarget_hi := inU_upper_last (r := r) (h := h) (e := e)
    (n := target) hp htU
  by_cases hy_large : h - 1 < y
  · have hyU := prefix_gt_h_sub_one_inU (r := r) (h := h) (e := e)
      (n := y) hp hy hy_large
    have hz_large : h - 1 < z := by omega
    have hzU := prefix_gt_h_sub_one_inU (r := r) (h := h) (e := e)
      (n := z) hp hz hz_large
    have hy_lo := inU_lower (r := r) (h := h) (e := e) (n := y) hp hyU
    have hz_lo := inU_lower (r := r) (h := h) (e := e) (n := z) hp hzU
    have hx_pos := residue_ge_one (r := r) (h := h) (e := e)
      (x := x) hp (Or.inl hx)
    have hgrid_lt_D := prev_grid_lt_D (r := r) (h := h) (e := e) hp
    have htop_lt := HHi_last_lt_two_D_add_one (r := r) (h := h) (e := e) hp
    omega
  · have hy_le : y <= h - 1 := by omega
    have hx_eq_one : x = 1 := by
      unfold InPrefix at hx
      rcases hx with hx1 | hxh | hxU
      · exact hx1
      · have hh := hp.h_ge_six
        omega
      · have hxlo := inU_lower (r := r) (h := h) (e := e) (n := x) hp hxU
        have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
        omega
    have hy_eq_h : y = h - 1 := by
      unfold InPrefix at hy
      rcases hy with hy1 | hyh | hyU
      · omega
      · exact hyh
      · have hylo := inU_lower (r := r) (h := h) (e := e) (n := y) hp hyU
        have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
        omega
    have hzU : InU r h e z := by
      have hz_gt : h - 1 < z := by omega
      exact prefix_gt_h_sub_one_inU (r := r) (h := h) (e := e)
        (n := z) hp hz hz_gt
    have htarget_eq : target = z + h := by
      rw [hx_eq_one, hy_eq_h] at hsum
      have hh := hp.h_ge_six
      omega
    rw [htarget_eq] at htU
    exact inU_add_h_not_inU (r := r) (h := h) (e := e) (n := z) hp hzU htU

/-- Prefix-band candidates are safe from triples of earlier candidates. -/
theorem prefix_candidate_safe {r h e target : Nat}
    (hp : Params r h e) (htU : InU r h e target) :
    ¬ CandidateTripleSumFrom r h e target := by
  intro htriple
  rcases htriple with ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum⟩
  have htarget_lt_M := inU_lt_M (r := r) (h := h) (e := e)
    (rho := target) hp htU
  have hxlt : x < M r h e := by omega
  have hylt : y < M r h e := by omega
  have hzltM : z < M r h e := by omega
  have hxP := candidate_lt_M_prefix (r := r) (h := h) (e := e)
    (n := x) hp hx hxlt
  have hyP := candidate_lt_M_prefix (r := r) (h := h) (e := e)
    (n := y) hp hy hylt
  have hzP := candidate_lt_M_prefix (r := r) (h := h) (e := e)
    (n := z) hp hz hzltM
  exact prefix_triple_sum_not_inU
    (r := r) (h := h) (e := e) (target := target) (x := x) (y := y) (z := z)
    hp htU hxP hyP hzP hxy hyz hsum

/--
Threshold wrapper for finite prefix safety: every prefix candidate at or above
the seed value `D` is safe from triples of earlier candidates.
-/
theorem prefix_candidate_safe_at_or_above_seed {r h e target : Nat}
    (hp : Params r h e) (htPrefix : InPrefix r h e target)
    (hseed : D r h e <= target) :
    ¬ CandidateTripleSumFrom r h e target := by
  unfold InPrefix at htPrefix
  rcases htPrefix with htarget | htarget | htU
  · have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
    have hh := hp.h_ge_six
    rw [htarget] at hseed
    omega
  · have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
    have hh := hp.h_ge_six
    rw [htarget] at hseed
    omega
  · exact prefix_candidate_safe (r := r) (h := h) (e := e)
      (target := target) hp htU

/--
Candidate-level prefix safety below the first period.  The hypotheses
`Candidate target` and `target < M` force prefix membership, then the threshold
wrapper applies.
-/
theorem candidate_below_M_safe_at_or_above_seed {r h e target : Nat}
    (hp : Params r h e) (htCandidate : Candidate r h e target)
    (htltM : target < M r h e) (hseed : D r h e <= target) :
    ¬ CandidateTripleSumFrom r h e target :=
  prefix_candidate_safe_at_or_above_seed
    (r := r) (h := h) (e := e) (target := target) hp
    (candidate_lt_M_prefix (r := r) (h := h) (e := e)
      (n := target) hp htCandidate htltM)
    hseed

/-- Strict-above-seed version of the finite prefix safety wrapper. -/
theorem candidate_below_M_safe_above_seed {r h e target : Nat}
    (hp : Params r h e) (htCandidate : Candidate r h e target)
    (htltM : target < M r h e) (hseed : D r h e < target) :
    ¬ CandidateTripleSumFrom r h e target :=
  candidate_below_M_safe_at_or_above_seed
    (r := r) (h := h) (e := e) (target := target)
    hp htCandidate htltM (by omega)

end RBand
end GreedyThreeSumfree
