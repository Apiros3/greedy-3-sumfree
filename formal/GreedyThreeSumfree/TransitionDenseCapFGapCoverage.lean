import GreedyThreeSumfree.TransitionDenseCapCoveragePredicates

namespace GreedyThreeSumfree
namespace TransitionDenseCap

theorem inQ_zero_of_inQ_one_gap {r h t u : Nat}
    (hu : InQ r h t 1 u) :
    InQ r h t 0 u := by
  unfold InQ at hu ⊢
  rcases hu with hfull | hterm
  · exact Or.inl hfull
  · exact Or.inr (by
      unfold InTerminalCap InInterval at hterm ⊢
      omega)

theorem D_add_inX_of_inQ_one_gap {r h t u : Nat}
    (hu : InQ r h t 1 u) :
    InX r h t (D r h t + u) := by
  unfold InX Shift
  exact ⟨u, hu, by omega⟩

theorem candidate_F_of_inQ_one_gap {r h t u : Nat}
    (hu : InQ r h t 1 u) :
    Candidate r h t (6 * D r h t + 1 + u) := by
  have hx : InX r h t (D r h t + u) :=
    D_add_inX_of_inQ_one_gap (r := r) (h := h) (t := t) (u := u) hu
  have hf : InF r h t (5 * D r h t + 1 + (D r h t + u)) := by
    unfold InF Shift
    exact ⟨D r h t + u, hx, rfl⟩
  have htarget :
      6 * D r h t + 1 + u = 5 * D r h t + 1 + (D r h t + u) := by
    omega
  rw [htarget]
  unfold Candidate
  exact Or.inr (Or.inr (Or.inr (Or.inl hf)))

theorem inQ_zero_le_D_add_one {r h t u : Nat}
    (hp : Params r h t) (hu : InQ r h t 0 u) :
    u <= D r h t + 1 := by
  unfold InQ at hu
  rcases hu with hfull | hterm
  · rcases hfull with ⟨i, hiFull⟩
    have hi : i < r := hiFull.1
    have huhi : u <= 2 * i * h + h - 1 := hiFull.2.2
    have hrun_lt :
        2 * i * h + h - 1 < 2 * r * h :=
      full_run_hi_lt_terminal_cap_lo
        (r := r) (h := h) (t := t) (i := i) hp hi
    have hD : 2 * r * h <= D r h t + 1 := by
      unfold D
      omega
    exact Nat.le_trans huhi (Nat.le_trans (Nat.le_of_lt hrun_lt) hD)
  · have huhi : u <= 2 * r * h + t + 1 := by
      unfold InTerminalCap InInterval at hterm
      exact hterm.2
    simpa [D] using huhi

theorem h_sub_one_lt_D_add {r h t x : Nat}
    (hp : Params r h t) :
    h - 1 < D r h t + x := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 1 <= 2 * r := by omega
  have hmul : h <= 2 * r * h := by
    simpa [Nat.one_mul] using Nat.mul_le_mul_right h hcoef
  unfold D
  omega

theorem coveredBySmallerCandidates_F_pair_of_QPairSumOrShift
    {r h t u : Nat} (hp : Params r h t)
    (hu : QPairSumOrShift r h t 0 1 u) :
    CoveredBySmallerCandidates r h t (7 * D r h t + 2 + u) := by
  rcases hu with hpair | hshift
  · rcases hpair with ⟨x, y, hx, hy, hsum⟩
    refine
      ⟨1, D r h t + x, 6 * D r h t + 1 + y,
        one_candidate r h t,
        inE_candidate (D_add_inE_of_inQ hx),
        candidate_F_of_inQ_one_gap hy,
        ?_, ?_, ?_, ?_⟩
    · have hD := D_ge_three hp
      omega
    · have hxhi := inQ_zero_le_D_add_one (r := r) (h := h) (t := t) hp hx
      have hD := D_ge_three hp
      omega
    · have hD := D_ge_three hp
      omega
    · omega
  · rcases hshift with ⟨m, hm, hshift⟩
    rcases hm with ⟨x, y, hx, hy, hsum⟩
    refine
      ⟨h - 1, D r h t + x, 6 * D r h t + 1 + y,
        h_sub_one_candidate r h t,
        inE_candidate (D_add_inE_of_inQ hx),
        candidate_F_of_inQ_one_gap hy,
        ?_, ?_, ?_, ?_⟩
    · exact h_sub_one_lt_D_add (r := r) (h := h) (t := t) (x := x) hp
    · have hxhi := inQ_zero_le_D_add_one (r := r) (h := h) (t := t) hp hx
      have hD := D_ge_three hp
      omega
    · have hD := D_ge_three hp
      have hh := hp.h_ge_six
      omega
    · have hh := hp.h_ge_six
      omega

theorem coveredBySmallerCandidates_F_twoE_of_restrictedTwoQ0PlusQSum
    {r h t u : Nat} (hp : Params r h t)
    (hu : RestrictedTwoQ0PlusQSum r h t 1 u) :
    CoveredBySmallerCandidates r h t (8 * D r h t + 1 + u) := by
  rcases hu with ⟨x, y, z, hx, hy, hz, hxy, hsum⟩
  refine
    ⟨D r h t + x, D r h t + y, 6 * D r h t + 1 + z,
      inE_candidate (D_add_inE_of_inQ hx),
      inE_candidate (D_add_inE_of_inQ hy),
      candidate_F_of_inQ_one_gap hz,
      ?_, ?_, ?_, ?_⟩
  · omega
  · have hyhi := inQ_zero_le_D_add_one (r := r) (h := h) (t := t) hp hy
    have hD := D_ge_three hp
    omega
  · have hD := D_ge_three hp
    omega
  · omega

theorem coveredBySmallerCandidates_dense_cap_F_pair_interval
    {r h t target : Nat} (hp : Params r h t)
    (htarget :
      InInterval (7 * D r h t + 2) (9 * D r h t + h + 1) target) :
    CoveredBySmallerCandidates r h t target := by
  let u := target - (7 * D r h t + 2)
  have huhi : u <= 2 * D r h t + h - 1 := by
    unfold InInterval at htarget
    dsimp [u]
    omega
  have hsum : target = 7 * D r h t + 2 + u := by
    unfold InInterval at htarget
    dsimp [u]
    omega
  rw [hsum]
  exact
    coveredBySmallerCandidates_F_pair_of_QPairSumOrShift
      (r := r) (h := h) (t := t) (u := u) hp
      (qPairSum_or_shift_dense_cap_coverage
        (r := r) (h := h) (t := t) (a := 0) (b := 1) (n := u)
        hp (by omega) (by omega) huhi)

theorem coveredBySmallerCandidates_dense_cap_F_twoE_interval
    {r h t target : Nat} (hp : Params r h t)
    (htarget :
      InInterval (8 * D r h t + 2) (11 * D r h t + 2) target) :
    CoveredBySmallerCandidates r h t target := by
  let u := target - (8 * D r h t + 1)
  have hulo : 1 <= u := by
    unfold InInterval at htarget
    dsimp [u]
    omega
  have huhi : u <= 3 * D r h t + 1 := by
    unfold InInterval at htarget
    dsimp [u]
    omega
  have hsum : target = 8 * D r h t + 1 + u := by
    unfold InInterval at htarget
    dsimp [u]
    omega
  rw [hsum]
  exact
    coveredBySmallerCandidates_F_twoE_of_restrictedTwoQ0PlusQSum
      (r := r) (h := h) (t := t) (u := u) hp
      (restrictedTwoQ0PlusQSum_dense_cap_pointwise_s1
        (r := r) (h := h) (t := t) (n := u) hp hulo huhi)

theorem coveredBySmallerCandidates_dense_cap_F_to_first_low_gap
    {r h t target : Nat} (hp : Params r h t)
    (htarget : InInterval (7 * D r h t + 2) (11 * D r h t + 2) target) :
    CoveredBySmallerCandidates r h t target := by
  by_cases hleft : target <= 9 * D r h t + h + 1
  · exact
      coveredBySmallerCandidates_dense_cap_F_pair_interval
        (r := r) (h := h) (t := t) (target := target) hp
        ⟨htarget.1, hleft⟩
  · have hright_lo : 8 * D r h t + 2 <= target := by
      omega
    exact
      coveredBySmallerCandidates_dense_cap_F_twoE_interval
        (r := r) (h := h) (t := t) (target := target) hp
        ⟨hright_lo, htarget.2⟩

end TransitionDenseCap
end GreedyThreeSumfree
