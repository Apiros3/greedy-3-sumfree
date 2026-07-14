import GreedyThreeSumfree.TransitionDenseCapFGapCoverage

namespace GreedyThreeSumfree
namespace TransitionDenseCap

private theorem M_le_q_mul_M {r h t q : Nat} (hq : 1 <= q) :
    M r h t <= q * M r h t := by
  have hmul : 1 * M r h t <= q * M r h t :=
    Nat.mul_le_mul_right (M r h t) hq
  simpa using hmul

private theorem D_add_q0_lt_positive_periodic {r h t q x rho : Nat}
    (hp : Params r h t) (hq : 1 <= q) (hx : InQ r h t 0 x) :
    D r h t + x < q * M r h t + rho := by
  have hxle := inQ_zero_le_D_add_one (r := r) (h := h) (t := t) hp hx
  have hMle := M_le_q_mul_M (r := r) (h := h) (t := t) hq
  have hltM : D r h t + x < M r h t := by
    unfold M
    omega
  have hqMle : q * M r h t <= q * M r h t + rho := by omega
  exact Nat.lt_of_lt_of_le hltM (Nat.le_trans hMle hqMle)

private theorem one_lt_D_add {r h t x : Nat} (hp : Params r h t) :
    1 < D r h t + x := by
  have hD := D_ge_three (r := r) (h := h) (t := t) hp
  omega

/--
Periodic low-to-high coverage from
`(1 + E + X_q) ∪ ((h-1) + E + X_q)`.

The packet input is `(Q_0 + Q_1) ∪ (h-2 + Q_0 + Q_1)`.
-/
theorem coveredBySmallerCandidates_periodic_low_pair_or_shift
    {r h t q u : Nat} (hp : Params r h t) (hq : 1 <= q)
    (hu : QPairSumOrShift r h t 0 1 u) :
    CoveredBySmallerCandidates r h t
      (q * M r h t + (2 * D r h t + 1 + u)) := by
  rcases hu with hpair | hshift
  · rcases hpair with ⟨x, y, hx, hy, hsum⟩
    refine
      ⟨1, D r h t + x, q * M r h t + (D r h t + y),
        one_candidate r h t,
        candidate_of_inQ_zero_shift (r := r) (h := h) (t := t) hx,
        candidate_of_periodic_inX
          (r := r) (h := h) (t := t) (q := q) (u := D r h t + y)
          hq (inX_of_inQ_one (r := r) (h := h) (t := t) hy),
        ?_, ?_, ?_, ?_⟩
    · exact one_lt_D_add (r := r) (h := h) (t := t) (x := x) hp
    · exact
        D_add_q0_lt_positive_periodic
          (r := r) (h := h) (t := t) (q := q) (x := x)
          (rho := D r h t + y) hp hq hx
    · have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    · omega
  · rcases hshift with ⟨m, hpair, hu_eq⟩
    rcases hpair with ⟨x, y, hx, hy, hsum⟩
    refine
      ⟨h - 1, D r h t + x, q * M r h t + (D r h t + y),
        h_sub_one_candidate r h t,
        candidate_of_inQ_zero_shift (r := r) (h := h) (t := t) hx,
        candidate_of_periodic_inX
          (r := r) (h := h) (t := t) (q := q) (u := D r h t + y)
          hq (inX_of_inQ_one (r := r) (h := h) (t := t) hy),
        ?_, ?_, ?_, ?_⟩
    · exact h_sub_one_lt_D_add (r := r) (h := h) (t := t) (x := x) hp
    · exact
        D_add_q0_lt_positive_periodic
          (r := r) (h := h) (t := t) (q := q) (x := x)
          (rho := D r h t + y) hp hq hx
    · have hD := D_ge_three (r := r) (h := h) (t := t) hp
      have hh := hp.h_ge_six
      omega
    · have hh := hp.h_ge_six
      omega

/--
Periodic low-to-high coverage from `X_q + (^2 E)`.

The packet input is `(^2 Q_0) + Q_1`; the two `Q_0` witnesses supply the
ordered distinct prefix `E` summands, while the `Q_1` witness supplies the
periodic `X` summand.
-/
theorem coveredBySmallerCandidates_periodic_low_twoE_plus_Q
    {r h t q u : Nat} (hp : Params r h t) (hq : 1 <= q)
    (hu : RestrictedTwoQ0PlusQSum r h t 1 u) :
    CoveredBySmallerCandidates r h t
      (q * M r h t + (3 * D r h t + u)) := by
  rcases hu with ⟨x, y, z, hx, hy, hz, hxy, hsum⟩
  refine
    ⟨D r h t + x, D r h t + y, q * M r h t + (D r h t + z),
      candidate_of_inQ_zero_shift (r := r) (h := h) (t := t) hx,
      candidate_of_inQ_zero_shift (r := r) (h := h) (t := t) hy,
      candidate_of_periodic_inX
        (r := r) (h := h) (t := t) (q := q) (u := D r h t + z)
        hq (inX_of_inQ_one (r := r) (h := h) (t := t) hz),
      ?_, ?_, ?_, ?_⟩
  · omega
  · exact
      D_add_q0_lt_positive_periodic
        (r := r) (h := h) (t := t) (q := q) (x := y)
        (rho := D r h t + z) hp hq hy
  · have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega
  · omega

/--
Dense-cap periodic low-to-high gap coverage.

For every positive block `q`, every offset
`o ∈ [2D+1, 6D+1]` is covered by three distinct smaller candidates.
-/
theorem coveredBySmallerCandidates_dense_cap_periodic_low_to_high_gap
    {r h t q o : Nat} (hp : Params r h t) (hq : 1 <= q)
    (ho : InInterval (2 * D r h t + 1) (6 * D r h t + 1) o) :
    CoveredBySmallerCandidates r h t (q * M r h t + o) := by
  by_cases hlow : o <= 4 * D r h t + h
  · let u := o - (2 * D r h t + 1)
    have holo : 2 * D r h t + 1 <= o := ho.1
    have huhi : u <= 2 * D r h t + h - 1 := by
      dsimp [u]
      omega
    have ho_eq : o = 2 * D r h t + 1 + u := by
      dsimp [u]
      omega
    rw [ho_eq]
    exact
      coveredBySmallerCandidates_periodic_low_pair_or_shift
        (r := r) (h := h) (t := t) (q := q) (u := u) hp hq
        (qPairSum_or_shift_dense_cap_coverage
          (r := r) (h := h) (t := t) (a := 0) (b := 1) (n := u)
          hp (by omega) (by omega) (by omega))
  · let u := o - 3 * D r h t
    have hohi : o <= 6 * D r h t + 1 := ho.2
    have hulo : 1 <= u := by
      dsimp [u]
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    have huhi : u <= 3 * D r h t + 1 := by
      dsimp [u]
      omega
    have ho_eq : o = 3 * D r h t + u := by
      dsimp [u]
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    rw [ho_eq]
    exact
      coveredBySmallerCandidates_periodic_low_twoE_plus_Q
        (r := r) (h := h) (t := t) (q := q) (u := u) hp hq
      (restrictedTwoQ0PlusQSum_dense_cap_pointwise_s1
        (r := r) (h := h) (t := t) (n := u) hp hulo huhi)

private theorem h_le_D_of_params_periodic {r h t : Nat} (hp : Params r h t) :
    h <= D r h t := by
  have hcoef : 1 <= 2 * r := by
    have hr := hp.r_pos
    omega
  have hmul : h <= 2 * r * h := by
    simpa [Nat.one_mul, Nat.mul_assoc] using Nat.mul_le_mul_right h hcoef
  unfold D
  omega

private theorem inQ_one_le_D_for_periodic {r h t u : Nat} (hp : Params r h t)
    (hu : InQ r h t 1 u) :
    u <= D r h t := by
  rcases hu with hfull | hterm
  · rcases hfull with ⟨i, hi⟩
    rcases hi with ⟨hir, hI⟩
    have hsucc : i + 1 <= r := by omega
    have hcoef : 2 * (i + 1) <= 2 * r := Nat.mul_le_mul_left 2 hsucc
    have hmul : 2 * (i + 1) * h <= 2 * r * h :=
      Nat.mul_le_mul_right h hcoef
    have hrew : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
      simp [Nat.left_distrib, Nat.right_distrib]
    unfold InInterval at hI
    unfold D
    rw [hrew] at hmul
    have hh := hp.h_ge_six
    omega
  · unfold InTerminalCap InInterval at hterm
    unfold D
    omega

private theorem candidate_periodic_X_of_inQ_one {r h t q u : Nat}
    (hq : 1 <= q) (hu : InQ r h t 1 u) :
    Candidate r h t (q * M r h t + (D r h t + u)) := by
  exact
    candidate_of_periodic_inX
      (r := r) (h := h) (t := t) (q := q) (u := D r h t + u)
      hq (inX_of_inQ_one (r := r) (h := h) (t := t) hu)

private theorem inY_of_inQ_two_high {r h t u : Nat}
    (hu : InQ r h t 2 u) :
    InY r h t (6 * D r h t + 2 + u) := by
  have hy : InY r h t (5 * D r h t + 2 + (D r h t + u)) :=
    inY_of_inW (r := r) (h := h) (t := t)
      (inW_of_inQ_two (r := r) (h := h) (t := t) hu)
  have hshift :
      6 * D r h t + 2 + u = 5 * D r h t + 2 + (D r h t + u) := by
    omega
  simpa [hshift] using hy

private theorem candidate_periodic_Y_of_inQ_two {r h t q u : Nat}
    (hq : 1 <= q) (hu : InQ r h t 2 u) :
    Candidate r h t (q * M r h t + (6 * D r h t + 2 + u)) := by
  exact
    candidate_of_periodic_inY
      (r := r) (h := h) (t := t) (q := q)
      (u := 6 * D r h t + 2 + u) hq
      (inY_of_inQ_two_high (r := r) (h := h) (t := t) hu)

/--
Periodic high-to-next-low coverage from
`(1 + F + X_q) union ((h-1) + F + X_q)`.

The packet input is `(Q_1 + Q_1) union (h-2 + Q_1 + Q_1)`.
-/
theorem coveredBySmallerCandidates_periodic_high_pair_or_shift
    {r h t q u : Nat} (hp : Params r h t) (hq : 1 <= q)
    (hu : QPairSumOrShift r h t 1 1 u) :
    CoveredBySmallerCandidates r h t
      (q * M r h t + (7 * D r h t + 2 + u)) := by
  rcases hu with hpair | hshift
  · rcases hpair with ⟨x, y, hx, hy, hsum⟩
    refine
      ⟨1, 6 * D r h t + 1 + x, q * M r h t + (D r h t + y),
        one_candidate r h t,
        candidate_F_of_inQ_one_gap (r := r) (h := h) (t := t) hx,
        candidate_periodic_X_of_inQ_one
          (r := r) (h := h) (t := t) (q := q) hq hy,
        ?_, ?_, ?_, ?_⟩
    · have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    · have hxle := inQ_one_le_D_for_periodic (r := r) (h := h) (t := t) hp hx
      have hqM : 10 * D r h t + 3 <= q * M r h t := by
        simpa [M, Nat.one_mul] using Nat.mul_le_mul_right (M r h t) hq
      omega
    · have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    · omega
  · rcases hshift with ⟨m, hpair, hu_eq⟩
    rcases hpair with ⟨x, y, hx, hy, hsum⟩
    refine
      ⟨h - 1, 6 * D r h t + 1 + x, q * M r h t + (D r h t + y),
        h_sub_one_candidate r h t,
        candidate_F_of_inQ_one_gap (r := r) (h := h) (t := t) hx,
        candidate_periodic_X_of_inQ_one
          (r := r) (h := h) (t := t) (q := q) hq hy,
        ?_, ?_, ?_, ?_⟩
    · have hhD := h_le_D_of_params_periodic (r := r) (h := h) (t := t) hp
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    · have hxle := inQ_one_le_D_for_periodic (r := r) (h := h) (t := t) hp hx
      have hqM : 10 * D r h t + 3 <= q * M r h t := by
        simpa [M, Nat.one_mul] using Nat.mul_le_mul_right (M r h t) hq
      omega
    · have hD := D_ge_three (r := r) (h := h) (t := t) hp
      have hh := hp.h_ge_six
      omega
    · have hh := hp.h_ge_six
      omega

/--
Periodic high-to-next-low coverage from `Y_q + (^2 E)`.

The packet input is `(^2 Q_0) + Q_2`; the two `Q_0` witnesses supply the
ordered distinct prefix `E` summands, while the `Q_2` witness supplies the
periodic `Y` summand.
-/
theorem coveredBySmallerCandidates_periodic_high_twoE_plus_Q
    {r h t q u : Nat} (hp : Params r h t) (hq : 1 <= q)
    (hu : RestrictedTwoQ0PlusQSum r h t 2 u) :
    CoveredBySmallerCandidates r h t
      (q * M r h t + (8 * D r h t + 2 + u)) := by
  rcases hu with ⟨x, y, z, hx, hy, hz, hxy, hsum⟩
  refine
    ⟨D r h t + x, D r h t + y,
      q * M r h t + (6 * D r h t + 2 + z),
      inE_candidate (D_add_inE_of_inQ hx),
      inE_candidate (D_add_inE_of_inQ hy),
      candidate_periodic_Y_of_inQ_two
        (r := r) (h := h) (t := t) (q := q) hq hz,
      ?_, ?_, ?_, ?_⟩
  · omega
  · have hyle := inQ_zero_le_D_add_one (r := r) (h := h) (t := t) hp hy
    have hqM : 10 * D r h t + 3 <= q * M r h t := by
      simpa [M, Nat.one_mul] using Nat.mul_le_mul_right (M r h t) hq
    omega
  · have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega
  · omega

theorem coveredBySmallerCandidates_dense_cap_periodic_high_pair_interval
    {r h t q o : Nat} (hp : Params r h t) (hq : 1 <= q)
    (ho : InInterval (7 * D r h t + 2) (9 * D r h t + h) o) :
    CoveredBySmallerCandidates r h t (q * M r h t + o) := by
  let u := o - (7 * D r h t + 2)
  have huhi : u <= 2 * D r h t + h - 2 := by
    unfold InInterval at ho
    dsimp [u]
    omega
  have ho_eq : o = 7 * D r h t + 2 + u := by
    unfold InInterval at ho
    dsimp [u]
    omega
  rw [ho_eq]
  exact
    coveredBySmallerCandidates_periodic_high_pair_or_shift
      (r := r) (h := h) (t := t) (q := q) (u := u) hp hq
      (qPairSum_or_shift_dense_cap_coverage
        (r := r) (h := h) (t := t) (a := 1) (b := 1) (n := u)
        hp (by omega) (by omega) huhi)

theorem coveredBySmallerCandidates_dense_cap_periodic_high_twoE_interval
    {r h t q o : Nat} (hp : Params r h t) (hq : 1 <= q)
    (ho : InInterval (8 * D r h t + 3) (11 * D r h t + 2) o) :
    CoveredBySmallerCandidates r h t (q * M r h t + o) := by
  let u := o - (8 * D r h t + 2)
  have hulo : 1 <= u := by
    unfold InInterval at ho
    dsimp [u]
    omega
  have huhi : u <= 3 * D r h t := by
    unfold InInterval at ho
    dsimp [u]
    omega
  have ho_eq : o = 8 * D r h t + 2 + u := by
    unfold InInterval at ho
    dsimp [u]
    omega
  rw [ho_eq]
  exact
    coveredBySmallerCandidates_periodic_high_twoE_plus_Q
      (r := r) (h := h) (t := t) (q := q) (u := u) hp hq
      (restrictedTwoQ0PlusQSum_dense_cap_pointwise_s2
        (r := r) (h := h) (t := t) (n := u) hp hulo huhi)

/--
Dense-cap periodic high-to-next-low gap coverage.

For every positive block `q`, every extended offset
`o in [7D+2, 11D+2]` is covered by three distinct smaller candidates. The
offset is intentionally kept extended, not reduced modulo `M`.
-/
theorem coveredBySmallerCandidates_dense_cap_periodic_high_to_next_low_gap
    {r h t q o : Nat} (hp : Params r h t) (hq : 1 <= q)
    (ho : InInterval (7 * D r h t + 2) (11 * D r h t + 2) o) :
    CoveredBySmallerCandidates r h t (q * M r h t + o) := by
  by_cases hleft : o <= 9 * D r h t + h
  · exact
      coveredBySmallerCandidates_dense_cap_periodic_high_pair_interval
        (r := r) (h := h) (t := t) (q := q) (o := o) hp hq
        ⟨ho.1, hleft⟩
  · have hright_lo : 8 * D r h t + 3 <= o := by
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      have hh := hp.h_ge_six
      omega
    exact
      coveredBySmallerCandidates_dense_cap_periodic_high_twoE_interval
        (r := r) (h := h) (t := t) (q := q) (o := o) hp hq
        ⟨hright_lo, ho.2⟩

end TransitionDenseCap
end GreedyThreeSumfree
