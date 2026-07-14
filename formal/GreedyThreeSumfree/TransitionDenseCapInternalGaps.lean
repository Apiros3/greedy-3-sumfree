import GreedyThreeSumfree.TransitionDenseCapPrefixSafety
import GreedyThreeSumfree.TransitionDenseCapPeriodicCoverage

namespace GreedyThreeSumfree.TransitionDenseCap

/--
If `u` lies in the internal gap after the `i`-th full run of a packet, then
`u - h` lies in that preceding full run.
-/
theorem internalGap_predecessor_inQ {r h t s i u : Nat}
    (hp : Params r h t) (hi : i < r)
    (hu : InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) u) :
    InQ r h t s (u - h) := by
  apply inQ_of_full_packet_run (i := i)
  unfold InFullPacketRun
  constructor
  · exact hi
  · unfold InInterval at hu ⊢
    constructor
    · have hh := hp.h_ge_six
      omega
    · have hh := hp.h_ge_six
      omega

/-- The predecessor of an internal `E`-gap point is an occupied `E` point. -/
theorem inE_internal_gap_predecessor {r h t i u : Nat}
    (hp : Params r h t) (hi : i < r)
    (hu : InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) u) :
    InE r h t (D r h t + (u - h)) := by
  exact
    D_add_inE_of_inQ
      (r := r) (h := h) (t := t) (u := u - h)
      (internalGap_predecessor_inQ
        (r := r) (h := h) (t := t) (s := 0) (i := i) (u := u) hp hi hu)

/-- The predecessor of an internal `F`-gap point is an occupied `F` point. -/
theorem inF_internal_gap_predecessor {r h t i u : Nat}
    (hp : Params r h t) (hi : i < r)
    (hu : InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) u) :
    InF r h t (6 * D r h t + 1 + (u - h)) := by
  have hq :
      InQ r h t 1 (u - h) :=
    internalGap_predecessor_inQ
      (r := r) (h := h) (t := t) (s := 1) (i := i) (u := u) hp hi hu
  have hx : InX r h t (D r h t + (u - h)) :=
    D_add_inX_of_inQ_one_gap (r := r) (h := h) (t := t) (u := u - h) hq
  have hf : InF r h t (5 * D r h t + 1 + (D r h t + (u - h))) := by
    unfold InF Shift
    exact ⟨D r h t + (u - h), hx, rfl⟩
  have htarget :
      6 * D r h t + 1 + (u - h) =
        5 * D r h t + 1 + (D r h t + (u - h)) := by
    omega
  rw [htarget]
  exact hf

/--
Every point in an internal gap of `E` is covered by `1 + (h - 1)` plus the
preceding occupied `E` point.
-/
theorem coveredBySmallerCandidates_E_internal_gap {r h t i u : Nat}
    (hp : Params r h t) (hi : i < r)
    (hu : InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) u) :
    CoveredBySmallerCandidates r h t (D r h t + u) := by
  have hpred :
      InE r h t (D r h t + (u - h)) :=
    inE_internal_gap_predecessor
      (r := r) (h := h) (t := t) (i := i) (u := u) hp hi hu
  refine
    ⟨1, h - 1, D r h t + (u - h),
      one_candidate r h t,
      h_sub_one_candidate r h t,
      inE_candidate hpred,
      ?_, ?_, ?_, ?_⟩
  · have hh := hp.h_ge_six
    omega
  · exact h_sub_one_lt_D_add (r := r) (h := h) (t := t) (x := u - h) hp
  · have hh := hp.h_ge_six
    unfold InInterval at hu
    omega
  · have hh := hp.h_ge_six
    unfold InInterval at hu
    omega

/--
Every point in an internal gap of `F` is covered by `1 + (h - 1)` plus the
preceding occupied `F` point.
-/
theorem coveredBySmallerCandidates_F_internal_gap {r h t i u : Nat}
    (hp : Params r h t) (hi : i < r)
    (hu : InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) u) :
    CoveredBySmallerCandidates r h t (6 * D r h t + 1 + u) := by
  have hq :
      InQ r h t 1 (u - h) :=
    internalGap_predecessor_inQ
      (r := r) (h := h) (t := t) (s := 1) (i := i) (u := u) hp hi hu
  refine
    ⟨1, h - 1, 6 * D r h t + 1 + (u - h),
      one_candidate r h t,
      h_sub_one_candidate r h t,
      candidate_F_of_inQ_one_gap (r := r) (h := h) (t := t) (u := u - h) hq,
      ?_, ?_, ?_, ?_⟩
  · have hh := hp.h_ge_six
    omega
  · have hbase :
        h - 1 < D r h t + (u - h) :=
      h_sub_one_lt_D_add (r := r) (h := h) (t := t) (x := u - h) hp
    omega
  · have hh := hp.h_ge_six
    unfold InInterval at hu
    omega
  · have hh := hp.h_ge_six
    unfold InInterval at hu
    omega

theorem candidateTripleSumFrom_E_internal_gap {r h t i u : Nat}
    (hp : Params r h t) (hi : i < r)
    (hu : InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) u) :
    CandidateTripleSumFrom r h t (D r h t + u) := by
  exact
    (candidateTripleSumFrom_iff_coveredBySmallerCandidates
      (r := r) (h := h) (t := t) (target := D r h t + u)).2
      (coveredBySmallerCandidates_E_internal_gap
        (r := r) (h := h) (t := t) (i := i) (u := u) hp hi hu)

theorem candidateTripleSumFrom_F_internal_gap {r h t i u : Nat}
    (hp : Params r h t) (hi : i < r)
    (hu : InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) u) :
    CandidateTripleSumFrom r h t (6 * D r h t + 1 + u) := by
  exact
    (candidateTripleSumFrom_iff_coveredBySmallerCandidates
      (r := r) (h := h) (t := t) (target := 6 * D r h t + 1 + u)).2
      (coveredBySmallerCandidates_F_internal_gap
        (r := r) (h := h) (t := t) (i := i) (u := u) hp hi hu)

private theorem h_le_D_of_params_internal {r h t : Nat} (hp : Params r h t) :
    h <= D r h t := by
  have hcoef : 1 <= 2 * r := by
    have hr := hp.r_pos
    omega
  have hmul : h <= 2 * r * h := by
    simpa [Nat.one_mul, Nat.mul_assoc] using Nat.mul_le_mul_right h hcoef
  unfold D
  omega

private theorem h_sub_one_lt_periodic_low_internal_summand
    {r h t q x : Nat} (hp : Params r h t) (hq : 1 <= q) :
    h - 1 < q * M r h t + (D r h t + x) := by
  have hh := hp.h_ge_six
  have hD := D_ge_three (r := r) (h := h) (t := t) hp
  have hhD := h_le_D_of_params_internal (r := r) (h := h) (t := t) hp
  have hMle : M r h t <= q * M r h t := by
    simpa [Nat.one_mul] using Nat.mul_le_mul_right (M r h t) hq
  unfold M at hMle ⊢
  omega

private theorem h_sub_one_lt_periodic_high_internal_summand
    {r h t q x : Nat} (hp : Params r h t) (hq : 1 <= q) :
    h - 1 < q * M r h t + (6 * D r h t + 2 + x) := by
  have hh := hp.h_ge_six
  have hD := D_ge_three (r := r) (h := h) (t := t) hp
  have hhD := h_le_D_of_params_internal (r := r) (h := h) (t := t) hp
  have hMle : M r h t <= q * M r h t := by
    simpa [Nat.one_mul] using Nat.mul_le_mul_right (M r h t) hq
  unfold M at hMle ⊢
  omega

private theorem preceding_full_run_offset_of_internal_gap
    {r h t i n : Nat} (hp : Params r h t)
    (hn : InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) n) :
    InInterval (2 * i * h) (2 * i * h + h - 1) (n - h) := by
  have hh := hp.h_ge_six
  unfold InInterval at hn ⊢
  constructor <;> omega

private theorem inY_of_inQ_two_internal_full_run {r h t u : Nat}
    (hu : InQ r h t 2 u) :
    InY r h t (6 * D r h t + 2 + u) := by
  have hy : InY r h t (5 * D r h t + 2 + (D r h t + u)) :=
    inY_of_inW (r := r) (h := h) (t := t)
      (inW_of_inQ_two (r := r) (h := h) (t := t) hu)
  have htarget :
      6 * D r h t + 2 + u = 5 * D r h t + 2 + (D r h t + u) := by
    omega
  simpa [htarget] using hy

/--
Internal gaps of the low periodic packet `q*M + X` are covered by the
preceding occupied low run shifted by `1 + (h - 1)`.
-/
theorem coveredBySmallerCandidates_periodic_low_internal_full_run_gap
    {r h t q i n : Nat} (hp : Params r h t) (hq : 1 <= q) (hi : i < r)
    (hn : InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) n) :
    CoveredBySmallerCandidates r h t (q * M r h t + (D r h t + n)) := by
  let x := n - h
  have hxI : InInterval (2 * i * h) (2 * i * h + h - 1) x := by
    dsimp [x]
    exact preceding_full_run_offset_of_internal_gap
      (r := r) (h := h) (t := t) (i := i) (n := n) hp hn
  have hxQ : InQ r h t 1 x :=
    full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 1) hi hxI
  have hxX : InX r h t (D r h t + x) :=
    inX_of_inQ_one (r := r) (h := h) (t := t) hxQ
  refine
    ⟨1, h - 1, q * M r h t + (D r h t + x),
      one_candidate r h t,
      h_sub_one_candidate r h t,
      candidate_of_periodic_inX
        (r := r) (h := h) (t := t) (q := q) (u := D r h t + x) hq hxX,
      ?_, ?_, ?_, ?_⟩
  · have hh := hp.h_ge_six
    omega
  · exact h_sub_one_lt_periodic_low_internal_summand
      (r := r) (h := h) (t := t) (q := q) (x := x) hp hq
  · have hh := hp.h_ge_six
    dsimp [x]
    unfold InInterval at hn
    omega
  · have hh := hp.h_ge_six
    dsimp [x]
    unfold InInterval at hn
    omega

/--
Internal gaps of the high periodic packet `q*M + Y` are covered by the
preceding occupied high run shifted by `1 + (h - 1)`.
-/
theorem coveredBySmallerCandidates_periodic_high_internal_full_run_gap
    {r h t q i n : Nat} (hp : Params r h t) (hq : 1 <= q) (hi : i < r)
    (hn : InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) n) :
    CoveredBySmallerCandidates r h t
      (q * M r h t + (6 * D r h t + 2 + n)) := by
  let x := n - h
  have hxI : InInterval (2 * i * h) (2 * i * h + h - 1) x := by
    dsimp [x]
    exact preceding_full_run_offset_of_internal_gap
      (r := r) (h := h) (t := t) (i := i) (n := n) hp hn
  have hxQ : InQ r h t 2 x :=
    full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 2) hi hxI
  have hxY : InY r h t (6 * D r h t + 2 + x) :=
    inY_of_inQ_two_internal_full_run (r := r) (h := h) (t := t) hxQ
  refine
    ⟨1, h - 1, q * M r h t + (6 * D r h t + 2 + x),
      one_candidate r h t,
      h_sub_one_candidate r h t,
      candidate_of_periodic_inY
        (r := r) (h := h) (t := t) (q := q)
        (u := 6 * D r h t + 2 + x) hq hxY,
      ?_, ?_, ?_, ?_⟩
  · have hh := hp.h_ge_six
    omega
  · exact h_sub_one_lt_periodic_high_internal_summand
      (r := r) (h := h) (t := t) (q := q) (x := x) hp hq
  · have hh := hp.h_ge_six
    dsimp [x]
    unfold InInterval at hn
    omega
  · have hh := hp.h_ge_six
    dsimp [x]
    unfold InInterval at hn
    omega

end GreedyThreeSumfree.TransitionDenseCap
