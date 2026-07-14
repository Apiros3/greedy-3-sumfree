import GreedyThreeSumfree.TransitionDenseCapTailClassification

namespace GreedyThreeSumfree
namespace TransitionDenseCap

/-- A prefix residue used as the actual candidate value in a decomposition. -/
def PrefixActualCandidate (r h t n sigma : Nat) : Prop :=
  Candidate r h t n ∧ n = sigma ∧ PrefixOnlyResidue r h t sigma

theorem quotient_carry_eq_of_sum_eq
    {m q q1 q2 q3 carry sigma1 sigma2 sigma3 rho : Nat}
    (hm : 0 < m)
    (hresidue : sigma1 + sigma2 + sigma3 = rho + carry * m)
    (hsum :
      (q1 * m + sigma1) + (q2 * m + sigma2) + (q3 * m + sigma3) =
        q * m + rho) :
    q1 + q2 + q3 + carry = q := by
  have hleft :
      (q1 * m + sigma1) + (q2 * m + sigma2) + (q3 * m + sigma3) =
        (q1 + q2 + q3 + carry) * m + rho := by
    calc
      (q1 * m + sigma1) + (q2 * m + sigma2) + (q3 * m + sigma3)
          = q1 * m + q2 * m + q3 * m + (sigma1 + sigma2 + sigma3) := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = q1 * m + q2 * m + q3 * m + (rho + carry * m) := by
            rw [hresidue]
      _ = (q1 + q2 + q3 + carry) * m + rho := by
            simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hcalc : (q1 + q2 + q3 + carry) * m + rho = q * m + rho := by
    rw [← hleft]
    exact hsum
  have hmuleq : (q1 + q2 + q3 + carry) * m = q * m :=
    Nat.add_right_cancel hcalc
  exact Nat.mul_right_cancel hm hmuleq

theorem dense_quotient_carry_eq_of_decomposed_sum
    {r h t q q1 q2 q3 carry sigma1 sigma2 sigma3 rho x y z target : Nat}
    (hx : x = q1 * M r h t + sigma1)
    (hy : y = q2 * M r h t + sigma2)
    (hz : z = q3 * M r h t + sigma3)
    (htarget : target = q * M r h t + rho)
    (hsum : x + y + z = target)
    (hresidue : sigma1 + sigma2 + sigma3 = rho + carry * M r h t) :
    q1 + q2 + q3 + carry = q := by
  rw [hx, hy, hz, htarget] at hsum
  exact quotient_carry_eq_of_sum_eq
    (m := M r h t) (q := q) (q1 := q1) (q2 := q2) (q3 := q3)
    (carry := carry) (sigma1 := sigma1) (sigma2 := sigma2) (sigma3 := sigma3)
    (rho := rho) M_pos hresidue hsum

theorem lowResidue_lt_M {r h t n : Nat}
    (hn : LowResidue r h t n) :
    n < M r h t := by
  unfold LowResidue InInterval at hn
  unfold M
  omega

theorem highResidue_lt_M {r h t n : Nat}
    (hn : HighResidue r h t n) :
    n < M r h t := by
  unfold HighResidue InInterval at hn
  unfold M
  omega

theorem smallResidue_lt_M {r h t n : Nat}
    (hp : Params r h t) (hn : SmallResidue h n) :
    n < M r h t := by
  have hnI := smallResidue_range (r := r) (h := h) (t := t) hp hn
  have hltD := h_sub_one_lt_D (r := r) (h := h) (t := t) hp
  have hDltM := D_lt_M (r := r) (h := h) (t := t)
  unfold InInterval at hnI
  omega

theorem allowedResidue_lt_M {r h t n : Nat}
    (hp : Params r h t) (hn : AllowedResidue r h t n) :
    n < M r h t := by
  rcases allowedResidue_category (r := r) (h := h) (t := t) (n := n) hp hn with
    hs | hlo | hhi
  · exact smallResidue_lt_M (r := r) (h := h) (t := t) hp hs
  · exact lowResidue_lt_M (r := r) (h := h) (t := t) hlo
  · exact highResidue_lt_M (r := r) (h := h) (t := t) hhi

theorem prefixOnlyResidue_lt_M {r h t n : Nat}
    (hp : Params r h t) (hn : PrefixOnlyResidue r h t n) :
    n < M r h t :=
  allowedResidue_lt_M (r := r) (h := h) (t := t) hp hn.1

theorem quotient_eq_zero_of_lt_period_decomposition
    {m q sigma n : Nat} (_hm : 0 < m)
    (hnlt : n < m) (hdecomp : n = q * m + sigma) :
    q = 0 := by
  by_cases hq : q = 0
  · exact hq
  · have hqpos : 1 <= q := by omega
    have hmle_qm : m <= q * m := by
      have hmul : 1 * m <= q * m := Nat.mul_le_mul_right m hqpos
      simpa using hmul
    have hmle_n : m <= n := by
      rw [hdecomp]
      omega
    omega

theorem quotient_eq_zero_of_prefixActualCandidate
    {r h t q sigma n : Nat} (hp : Params r h t)
    (hn : PrefixActualCandidate r h t n sigma)
    (hdecomp : n = q * M r h t + sigma) :
    q = 0 := by
  have hsigma_lt := prefixOnlyResidue_lt_M (r := r) (h := h) (t := t) hp hn.2.2
  have hnlt : n < M r h t := by
    rw [hn.2.1]
    exact hsigma_lt
  exact quotient_eq_zero_of_lt_period_decomposition
    (m := M r h t) M_pos hnlt hdecomp

theorem prefixActualTriple_quotients_zero
    {r h t q1 q2 q3 sigma1 sigma2 sigma3 n1 n2 n3 : Nat}
    (hp : Params r h t)
    (hn1 : PrefixActualCandidate r h t n1 sigma1)
    (hn2 : PrefixActualCandidate r h t n2 sigma2)
    (hn3 : PrefixActualCandidate r h t n3 sigma3)
    (hdecomp1 : n1 = q1 * M r h t + sigma1)
    (hdecomp2 : n2 = q2 * M r h t + sigma2)
    (hdecomp3 : n3 = q3 * M r h t + sigma3) :
    q1 = 0 ∧ q2 = 0 ∧ q3 = 0 := by
  exact
    ⟨quotient_eq_zero_of_prefixActualCandidate
        (r := r) (h := h) (t := t) (q := q1) (sigma := sigma1) (n := n1)
        hp hn1 hdecomp1,
      quotient_eq_zero_of_prefixActualCandidate
        (r := r) (h := h) (t := t) (q := q2) (sigma := sigma2) (n := n2)
        hp hn2 hdecomp2,
      quotient_eq_zero_of_prefixActualCandidate
        (r := r) (h := h) (t := t) (q := q3) (sigma := sigma3) (n := n3)
        hp hn3 hdecomp3⟩

theorem inF_not_inX {r h t n : Nat}
    (hp : Params r h t) (hF : InF r h t n) :
    ¬ InX r h t n := by
  intro hX
  have hFI := inF_residue_range (r := r) (h := h) (t := t) hp hF
  have hXI := inX_residue_range (r := r) (h := h) (t := t) hp hX
  have hD := D_ge_three (r := r) (h := h) (t := t) hp
  unfold HighResidue InInterval at hFI
  unfold LowResidue InInterval at hXI
  omega

theorem inF_notY_prefixOnlyResidue {r h t n : Nat}
    (hp : Params r h t) (hF : InF r h t n) (hnotY : ¬ InY r h t n) :
    PrefixOnlyResidue r h t n := by
  constructor
  · unfold AllowedResidue SigmaResidue
    exact Or.inr (Or.inr (Or.inl hF))
  · intro htail
    rcases htail with hX | hY
    · exact inF_not_inX (r := r) (h := h) (t := t) hp hF hX
    · exact hnotY hY

theorem smallSmallFGapHit_prefixOnlyResidues
    {r h t rho x y z : Nat} (hp : Params r h t)
    (hhit : SmallSmallFGapHit r h t rho x y z) :
    PrefixOnlyResidue r h t x ∧
      PrefixOnlyResidue r h t y ∧ PrefixOnlyResidue r h t z := by
  rcases hhit with ⟨hsmall, hF, hnotY, _hrho⟩
  constructor
  · rcases hsmall with hxy | hxy
    · exact smallResidue_prefixOnlyResidue
        (r := r) (h := h) (t := t) hp (Or.inl hxy.1)
    · exact smallResidue_prefixOnlyResidue
        (r := r) (h := h) (t := t) hp (Or.inr hxy.1)
  · constructor
    · rcases hsmall with hxy | hxy
      · exact smallResidue_prefixOnlyResidue
          (r := r) (h := h) (t := t) hp (Or.inr hxy.2)
      · exact smallResidue_prefixOnlyResidue
          (r := r) (h := h) (t := t) hp (Or.inl hxy.2)
    · exact inF_notY_prefixOnlyResidue
        (r := r) (h := h) (t := t) hp hF hnotY

theorem smallSmallFGapHit_residue_sum_eq_rho
    {r h t rho x y z : Nat} (hp : Params r h t)
    (hhit : SmallSmallFGapHit r h t rho x y z) :
    x + y + z = rho := by
  rcases hhit with ⟨hsmall, _hF, _hnotY, hrho⟩
  rcases hsmall with hxy | hxy
  · rw [hxy.1, hxy.2, hrho]
    have hh := hp.h_ge_six
    omega
  · rw [hxy.1, hxy.2, hrho]
    have hh := hp.h_ge_six
    omega

theorem smallSmallFGapHit_prefixActualCandidates
    {r h t rho x y z : Nat} (hp : Params r h t)
    (hhit : SmallSmallFGapHit r h t rho x y z)
    (hx : Candidate r h t x) (hy : Candidate r h t y) (hz : Candidate r h t z) :
    PrefixActualCandidate r h t x x ∧
      PrefixActualCandidate r h t y y ∧ PrefixActualCandidate r h t z z := by
  have hprefix := smallSmallFGapHit_prefixOnlyResidues
    (r := r) (h := h) (t := t) hp hhit
  exact ⟨⟨hx, rfl, hprefix.1⟩, ⟨hy, rfl, hprefix.2.1⟩, ⟨hz, rfl, hprefix.2.2⟩⟩

theorem smallSmallFGapHit_quotients_zero
    {r h t q1 q2 q3 rho x y z : Nat}
    (hp : Params r h t)
    (hhit : SmallSmallFGapHit r h t rho x y z)
    (hx : Candidate r h t x) (hy : Candidate r h t y) (hz : Candidate r h t z)
    (hdecompX : x = q1 * M r h t + x)
    (hdecompY : y = q2 * M r h t + y)
    (hdecompZ : z = q3 * M r h t + z) :
    q1 = 0 ∧ q2 = 0 ∧ q3 = 0 := by
  rcases smallSmallFGapHit_prefixActualCandidates
      (r := r) (h := h) (t := t) hp hhit hx hy hz with
    ⟨hpx, hpy, hpz⟩
  exact prefixActualTriple_quotients_zero
    (r := r) (h := h) (t := t)
    (q1 := q1) (q2 := q2) (q3 := q3)
    (sigma1 := x) (sigma2 := y) (sigma3 := z)
    (n1 := x) (n2 := y) (n3 := z)
    hp hpx hpy hpz hdecompX hdecompY hdecompZ

theorem carry_zero_prefix_quotients_force_target_block_zero
    {q q1 q2 q3 carry : Nat}
    (hquot : q1 + q2 + q3 + carry = q)
    (hzeros : q1 = 0 ∧ q2 = 0 ∧ q3 = 0)
    (hcarry : carry = 0) :
    q = 0 := by
  omega

theorem smallSmallFGapHit_carry_zero_forces_target_block_zero
    {r h t q q1 q2 q3 carry rho x y z : Nat}
    (_hhit : SmallSmallFGapHit r h t rho x y z)
    (hquot : q1 + q2 + q3 + carry = q)
    (hzeros : q1 = 0 ∧ q2 = 0 ∧ q3 = 0)
    (hcarry : carry = 0) :
    q = 0 := by
  exact carry_zero_prefix_quotients_force_target_block_zero hquot hzeros hcarry

theorem smallSmallFGapHit_carry_zero_positive_block_false
    {r h t q q1 q2 q3 carry rho x y z : Nat}
    (hq : 1 <= q)
    (hhit : SmallSmallFGapHit r h t rho x y z)
    (hquot : q1 + q2 + q3 + carry = q)
    (hzeros : q1 = 0 ∧ q2 = 0 ∧ q3 = 0)
    (hcarry : carry = 0) :
    False := by
  have hqzero := smallSmallFGapHit_carry_zero_forces_target_block_zero
    (r := r) (h := h) (t := t) (q := q)
    (q1 := q1) (q2 := q2) (q3 := q3) (carry := carry)
    (rho := rho) (x := x) (y := y) (z := z)
    hhit hquot hzeros hcarry
  omega

theorem smallSmallFGapHit_decomposed_positive_block_false
    {r h t q q1 q2 q3 carry rho target n1 n2 n3 sigma1 sigma2 sigma3 : Nat}
    (hp : Params r h t) (hq : 1 <= q)
    (hhit : SmallSmallFGapHit r h t rho sigma1 sigma2 sigma3)
    (hn1 : Candidate r h t n1) (hn2 : Candidate r h t n2)
    (hn3 : Candidate r h t n3)
    (hn1_actual : n1 = sigma1) (hn2_actual : n2 = sigma2)
    (hn3_actual : n3 = sigma3)
    (hdecomp1 : n1 = q1 * M r h t + sigma1)
    (hdecomp2 : n2 = q2 * M r h t + sigma2)
    (hdecomp3 : n3 = q3 * M r h t + sigma3)
    (htarget : target = q * M r h t + rho)
    (hsum : n1 + n2 + n3 = target)
    (hcarry : carry = 0) :
    False := by
  have hresidue0 := smallSmallFGapHit_residue_sum_eq_rho
    (r := r) (h := h) (t := t) hp hhit
  have hresidue :
      sigma1 + sigma2 + sigma3 = rho + carry * M r h t := by
    rw [hcarry, Nat.zero_mul, Nat.add_zero]
    exact hresidue0
  have hquot := dense_quotient_carry_eq_of_decomposed_sum
    (r := r) (h := h) (t := t) (q := q)
    (q1 := q1) (q2 := q2) (q3 := q3) (carry := carry)
    (sigma1 := sigma1) (sigma2 := sigma2) (sigma3 := sigma3)
    (rho := rho) (x := n1) (y := n2) (z := n3) (target := target)
    hdecomp1 hdecomp2 hdecomp3 htarget hsum hresidue
  have hprefix := smallSmallFGapHit_prefixOnlyResidues
    (r := r) (h := h) (t := t) hp hhit
  have hp1 : PrefixActualCandidate r h t n1 sigma1 :=
    ⟨hn1, hn1_actual, hprefix.1⟩
  have hp2 : PrefixActualCandidate r h t n2 sigma2 :=
    ⟨hn2, hn2_actual, hprefix.2.1⟩
  have hp3 : PrefixActualCandidate r h t n3 sigma3 :=
    ⟨hn3, hn3_actual, hprefix.2.2⟩
  have hzeros := prefixActualTriple_quotients_zero
    (r := r) (h := h) (t := t)
    (q1 := q1) (q2 := q2) (q3 := q3)
    (sigma1 := sigma1) (sigma2 := sigma2) (sigma3 := sigma3)
    (n1 := n1) (n2 := n2) (n3 := n3)
    hp hp1 hp2 hp3 hdecomp1 hdecomp2 hdecomp3
  exact smallSmallFGapHit_carry_zero_positive_block_false
    (r := r) (h := h) (t := t) (q := q)
    (q1 := q1) (q2 := q2) (q3 := q3) (carry := carry)
    (rho := rho) (x := sigma1) (y := sigma2) (z := sigma3)
    hq hhit hquot hzeros hcarry

end TransitionDenseCap
end GreedyThreeSumfree
