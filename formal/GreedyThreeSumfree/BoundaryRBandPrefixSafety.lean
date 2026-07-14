import GreedyThreeSumfree.BoundaryRBandPrefixCoverage

namespace GreedyThreeSumfree
namespace BoundaryRBand

theorem candidate_lt_M_prefix {r h n : Nat} (_hp : Params r h)
    (hn : Candidate r h n) (hnlt : n < M r h) :
    InPrefix r h n := by
  rcases hn with hpfx | hblock
  · exact hpfx
  · rcases hblock with ⟨q, hq, hnblock⟩
    have hMle := periodic_block_ge_M (r := r) (h := h)
      (q := q) (n := n) hq hnblock
    omega

theorem inU_lower {r h n : Nat} (_hp : Params r h)
    (hn : InU r h n) :
    D r h <= n := by
  rcases hn with ⟨i, _hi, hnH⟩
  unfold InH InInterval HLo at hnH
  omega

theorem inU_upper_last {r h n : Nat} (hp : Params r h)
    (hn : InU r h n) :
    n <= HHi r h (r - 1) := by
  rcases hn with ⟨i, hi, hnH⟩
  have hlast : i <= r - 1 := by
    have hr := hp.r_pos
    omega
  have hmono := HHi_mono_index (r := r) (h := h) hlast
  exact Nat.le_trans hnH.2 hmono

theorem c_eq_two_D_add_one {r h : Nat} (hp : Params r h) :
    c r h = 2 * D r h + 1 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hprod : 2 * ((2 * r) * h) = (4 * r) * h := by
    have hcoef : 2 * (2 * r) = 4 * r := by omega
    rw [← Nat.mul_assoc, hcoef]
  have hApos : 1 <= (2 * r) * h := by
    have hcoef : 1 <= 2 * r := by omega
    have hmul : 1 * h <= (2 * r) * h :=
      Nat.mul_le_mul_right h hcoef
    omega
  unfold D c
  rw [← hprod]
  omega

theorem HHi_last_add_h_add_one_eq_c {r h : Nat} (hp : Params r h) :
    HHi r h (r - 1) + h + 1 = c r h := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hprod :
      (2 * r) * h + (2 * (r - 1)) * h + 2 * h = (4 * r) * h := by
    calc
      (2 * r) * h + (2 * (r - 1)) * h + 2 * h
          = (2 * r + 2 * (r - 1)) * h + 2 * h := by
              rw [← Nat.add_mul]
      _ = (2 * r + 2 * (r - 1) + 2) * h := by
              rw [← Nat.add_mul]
      _ = (4 * r) * h := by
              have hcoef : 2 * r + 2 * (r - 1) + 2 = 4 * r := by omega
              rw [hcoef]
  have hApos : 1 <= (2 * r) * h := by
    have hcoef : 1 <= 2 * r := by omega
    have hmul : 1 * h <= (2 * r) * h :=
      Nat.mul_le_mul_right h hcoef
    omega
  unfold HHi HLo D c
  rw [← hprod]
  omega

theorem HHi_last_add_h_lt_c {r h : Nat} (hp : Params r h) :
    HHi r h (r - 1) + h < c r h := by
  have heq := HHi_last_add_h_add_one_eq_c (r := r) (h := h) hp
  omega

theorem prefix_gt_h_sub_one_lt_c_inU {r h n : Nat}
    (hp : Params r h) (hn : InPrefix r h n)
    (hgt : h - 1 < n) (hnltc : n < c r h) :
    InU r h n := by
  unfold InPrefix at hn
  rcases hn with rfl | rfl | rfl | hU
  · have hh := hp.h_ge_six
    omega
  · omega
  · omega
  · exact hU

theorem inH_add_h_not_inU {r h i n : Nat} (hp : Params r h)
    (_hi : i < r) (hn : InH r h i n) :
    ¬ InU r h (n + h) := by
  intro hU
  rcases hU with ⟨j, _hj, hjH⟩
  by_cases hij : i < j
  · have hn_hi : n <= HHi r h i := hn.2
    have hnh_lt : n + h < HLo r h j := by
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
    have hj_hi_le : HHi r h j <= HHi r h i := by
      have hcoef : 2 * j <= 2 * i := Nat.mul_le_mul_left 2 hji
      have hprod : 2 * j * h <= 2 * i * h :=
        Nat.mul_le_mul_right h hcoef
      unfold HHi HLo
      omega
    have hnh_gt : HHi r h i < n + h := by
      have hh := hp.h_ge_six
      have hn_lo : HLo r h i <= n := hn.1
      unfold HHi
      omega
    exact (Nat.not_lt_of_ge (Nat.le_trans hjH.2 hj_hi_le)) hnh_gt

theorem inU_add_h_not_inU {r h n : Nat} (hp : Params r h)
    (hn : InU r h n) :
    ¬ InU r h (n + h) := by
  rcases hn with ⟨i, hi, hnH⟩
  exact inH_add_h_not_inU (r := r) (h := h) (i := i) (n := n)
    hp hi hnH

theorem prefix_triple_sum_not_inU {r h target x y z : Nat}
    (hp : Params r h)
    (htU : InU r h target)
    (hx : InPrefix r h x) (hy : InPrefix r h y) (hz : InPrefix r h z)
    (hxy : x < y) (hyz : y < z) (hzlt : z < target)
    (hsum : x + y + z = target) :
    False := by
  have htarget_lt_c := inU_lt_c (r := r) (h := h) hp htU
  by_cases hy_large : h - 1 < y
  · have hyltc : y < c r h := by omega
    have hzltc : z < c r h := by omega
    have hyU := prefix_gt_h_sub_one_lt_c_inU
      (r := r) (h := h) (n := y) hp hy hy_large hyltc
    have hz_large : h - 1 < z := by omega
    have hzU := prefix_gt_h_sub_one_lt_c_inU
      (r := r) (h := h) (n := z) hp hz hz_large hzltc
    have hy_lo := inU_lower (r := r) (h := h) (n := y) hp hyU
    have hz_lo := inU_lower (r := r) (h := h) (n := z) hp hzU
    have hx_pos := residue_ge_one (r := r) (h := h)
      (x := x) hp (Or.inl hx)
    have hc_eq := c_eq_two_D_add_one (r := r) (h := h) hp
    omega
  · have hy_le : y <= h - 1 := by omega
    have hx_eq_one : x = 1 := by
      unfold InPrefix at hx
      rcases hx with hx1 | hxh | hxc | hxU
      · exact hx1
      · have hh := hp.h_ge_six
        omega
      · have hD := D_ge_h_add_one (r := r) (h := h) hp
        have hDc := D_lt_c (r := r) (h := h) hp
        rw [hxc] at hxy
        omega
      · have hxlo := inU_lower (r := r) (h := h) (n := x) hp hxU
        have hD := D_ge_h_add_one (r := r) (h := h) hp
        omega
    have hy_eq_h : y = h - 1 := by
      unfold InPrefix at hy
      rcases hy with hy1 | hyh | hyc | hyU
      · have hx_pos := residue_ge_one (r := r) (h := h)
          (x := x) hp (Or.inl hx)
        omega
      · exact hyh
      · have hD := D_ge_h_add_one (r := r) (h := h) hp
        have hDc := D_lt_c (r := r) (h := h) hp
        rw [hyc] at hy_le
        omega
      · have hylo := inU_lower (r := r) (h := h) (n := y) hp hyU
        have hD := D_ge_h_add_one (r := r) (h := h) hp
        omega
    have hzltc : z < c r h := by omega
    have hzU : InU r h z := by
      have hz_gt : h - 1 < z := by omega
      exact prefix_gt_h_sub_one_lt_c_inU (r := r) (h := h)
        (n := z) hp hz hz_gt hzltc
    have htarget_eq : target = z + h := by
      rw [hx_eq_one, hy_eq_h] at hsum
      have hh := hp.h_ge_six
      omega
    rw [htarget_eq] at htU
    exact inU_add_h_not_inU (r := r) (h := h) (n := z) hp hzU htU

theorem prefix_triple_sum_not_c {r h x y z : Nat}
    (hp : Params r h)
    (hx : InPrefix r h x) (hy : InPrefix r h y) (hz : InPrefix r h z)
    (hxy : x < y) (hyz : y < z) (hzlt : z < c r h)
    (hsum : x + y + z = c r h) :
    False := by
  by_cases hy_large : h - 1 < y
  · have hyltc : y < c r h := by omega
    have hyU := prefix_gt_h_sub_one_lt_c_inU
      (r := r) (h := h) (n := y) hp hy hy_large hyltc
    have hz_large : h - 1 < z := by omega
    have hzU := prefix_gt_h_sub_one_lt_c_inU
      (r := r) (h := h) (n := z) hp hz hz_large hzlt
    have hy_lo := inU_lower (r := r) (h := h) (n := y) hp hyU
    have hz_lo := inU_lower (r := r) (h := h) (n := z) hp hzU
    have hx_pos := residue_ge_one (r := r) (h := h)
      (x := x) hp (Or.inl hx)
    have hc_eq := c_eq_two_D_add_one (r := r) (h := h) hp
    omega
  · have hy_le : y <= h - 1 := by omega
    have hx_eq_one : x = 1 := by
      unfold InPrefix at hx
      rcases hx with hx1 | hxh | hxc | hxU
      · exact hx1
      · have hh := hp.h_ge_six
        omega
      · have hD := D_ge_h_add_one (r := r) (h := h) hp
        have hDc := D_lt_c (r := r) (h := h) hp
        rw [hxc] at hxy
        omega
      · have hxlo := inU_lower (r := r) (h := h) (n := x) hp hxU
        have hD := D_ge_h_add_one (r := r) (h := h) hp
        omega
    have hy_eq_h : y = h - 1 := by
      unfold InPrefix at hy
      rcases hy with hy1 | hyh | hyc | hyU
      · have hx_pos := residue_ge_one (r := r) (h := h)
          (x := x) hp (Or.inl hx)
        omega
      · exact hyh
      · have hD := D_ge_h_add_one (r := r) (h := h) hp
        have hDc := D_lt_c (r := r) (h := h) hp
        rw [hyc] at hy_le
        omega
      · have hylo := inU_lower (r := r) (h := h) (n := y) hp hyU
        have hD := D_ge_h_add_one (r := r) (h := h) hp
        omega
    have hzU : InU r h z := by
      have hz_gt : h - 1 < z := by omega
      exact prefix_gt_h_sub_one_lt_c_inU (r := r) (h := h)
        (n := z) hp hz hz_gt hzlt
    have hz_hi := inU_upper_last (r := r) (h := h) (n := z) hp hzU
    have hlast_lt_c := HHi_last_add_h_lt_c (r := r) (h := h) hp
    rw [hx_eq_one, hy_eq_h] at hsum
    have hh := hp.h_ge_six
    omega

theorem inU_candidate_safe {r h target : Nat}
    (hp : Params r h) (htU : InU r h target) :
    ¬ CandidateTripleSumFrom r h target := by
  intro htriple
  rcases htriple with ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum⟩
  have htarget_lt_M := inU_lt_M (r := r) (h := h)
    (rho := target) hp htU
  have hxlt : x < M r h := by omega
  have hylt : y < M r h := by omega
  have hzltM : z < M r h := by omega
  have hxP := candidate_lt_M_prefix (r := r) (h := h)
    (n := x) hp hx hxlt
  have hyP := candidate_lt_M_prefix (r := r) (h := h)
    (n := y) hp hy hylt
  have hzP := candidate_lt_M_prefix (r := r) (h := h)
    (n := z) hp hz hzltM
  exact prefix_triple_sum_not_inU
    (r := r) (h := h) (target := target) (x := x) (y := y) (z := z)
    hp htU hxP hyP hzP hxy hyz hzlt hsum

theorem singleton_c_safe {r h : Nat} (hp : Params r h) :
    ¬ CandidateTripleSumFrom r h (c r h) := by
  intro htriple
  rcases htriple with ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum⟩
  have hc_lt_M := c_lt_M (r := r) (h := h) hp
  have hxlt : x < M r h := by omega
  have hylt : y < M r h := by omega
  have hzltM : z < M r h := by omega
  have hxP := candidate_lt_M_prefix (r := r) (h := h)
    (n := x) hp hx hxlt
  have hyP := candidate_lt_M_prefix (r := r) (h := h)
    (n := y) hp hy hylt
  have hzP := candidate_lt_M_prefix (r := r) (h := h)
    (n := z) hp hz hzltM
  exact prefix_triple_sum_not_c
    (r := r) (h := h) (x := x) (y := y) (z := z)
    hp hxP hyP hzP hxy hyz hzlt hsum

/--
Strict finite-prefix safety above the third seed.  This covers the prefix
intervals `U` and the isolated boundary point `c`.
-/
theorem prefix_candidate_safe {r h target : Nat}
    (hp : Params r h) (htPrefix : InPrefix r h target)
    (hseed : D r h < target) :
    ¬ CandidateTripleSumFrom r h target := by
  unfold InPrefix at htPrefix
  rcases htPrefix with htarget | htarget | htarget | htU
  · rw [htarget] at hseed
    have hD := D_ge_three (r := r) (h := h) hp
    omega
  · rw [htarget] at hseed
    have hD := D_ge_h_add_one (r := r) (h := h) hp
    omega
  · rw [htarget]
    exact singleton_c_safe (r := r) (h := h) hp
  · exact inU_candidate_safe (r := r) (h := h)
      (target := target) hp htU

/--
Finite-prefix safety at or above the seed value `D`.  The endpoint `D` itself
is included because it lies in `H_0` and is not a triple of earlier candidates.
-/
theorem prefix_candidate_safe_at_or_above_seed {r h target : Nat}
    (hp : Params r h) (htPrefix : InPrefix r h target)
    (hseed : D r h <= target) :
    ¬ CandidateTripleSumFrom r h target := by
  unfold InPrefix at htPrefix
  rcases htPrefix with htarget | htarget | htarget | htU
  · rw [htarget] at hseed
    have hD := D_ge_three (r := r) (h := h) hp
    omega
  · rw [htarget] at hseed
    have hD := D_ge_h_add_one (r := r) (h := h) hp
    omega
  · rw [htarget]
    exact singleton_c_safe (r := r) (h := h) hp
  · exact inU_candidate_safe (r := r) (h := h)
      (target := target) hp htU

/--
Candidate-level prefix safety below the first period.  The hypotheses
`Candidate target` and `target < M` force prefix membership, then the threshold
wrapper applies.
-/
theorem candidate_below_M_safe_at_or_above_seed {r h target : Nat}
    (hp : Params r h) (htCandidate : Candidate r h target)
    (htltM : target < M r h) (hseed : D r h <= target) :
    ¬ CandidateTripleSumFrom r h target :=
  prefix_candidate_safe_at_or_above_seed
    (r := r) (h := h) (target := target) hp
    (candidate_lt_M_prefix (r := r) (h := h)
      (n := target) hp htCandidate htltM)
    hseed

theorem periodic_block_gt_finalPrefixGapHi {r h q n : Nat}
    (hp : Params r h) (hq : 1 <= q)
    (hn : InPeriodicBlock r h q n) :
    finalPrefixGapHi r h < n := by
  rcases hn with ⟨rho, hrho, rfl⟩
  have hMle : M r h <= q * M r h := by
    have hmul : 1 * M r h <= q * M r h :=
      Nat.mul_le_mul_right (M r h) hq
    simpa using hmul
  have hrho_lo := inV_lower (r := r) (h := h) hp hrho
  have hD := D_ge_three (r := r) (h := h) hp
  unfold finalPrefixGapHi VBot at *
  omega

theorem candidate_le_finalPrefixGapHi_prefix {r h z : Nat}
    (hp : Params r h)
    (hz : Candidate r h z)
    (hzle : z <= finalPrefixGapHi r h) :
    InPrefix r h z := by
  rcases hz with hpfx | hblock
  · exact hpfx
  · rcases hblock with ⟨q, hq, hzblock⟩
    have hgt := periodic_block_gt_finalPrefixGapHi
      (r := r) (h := h) (q := q) (n := z) hp hq hzblock
    omega

theorem prefix_window_candidate_safe {r h z : Nat}
    (hp : Params r h)
    (hzD : D r h < z)
    (hzle : z <= finalPrefixGapHi r h)
    (hz : Candidate r h z) :
    ¬ CandidateTripleSumFrom r h z := by
  have hzPrefix := candidate_le_finalPrefixGapHi_prefix
    (r := r) (h := h) (z := z) hp hz hzle
  exact prefix_candidate_safe
    (r := r) (h := h) (target := z) hp hzPrefix hzD

end BoundaryRBand
end GreedyThreeSumfree
