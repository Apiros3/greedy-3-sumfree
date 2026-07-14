import GreedyThreeSumfree.TransitionDenseCapFGapCoverage

namespace GreedyThreeSumfree
namespace TransitionDenseCap

/-- Local ordered distinct smaller-candidate three-sum predicate. -/
def CandidateTripleSumFrom (r h t target : Nat) : Prop :=
  ∃ x y z : Nat,
    Candidate r h t x ∧
    Candidate r h t y ∧
    Candidate r h t z ∧
    x < y ∧
    y < z ∧
    z < target ∧
    x + y + z = target

theorem candidateTripleSumFrom_iff_coveredBySmallerCandidates
    {r h t target : Nat} :
    CandidateTripleSumFrom r h t target ↔
      CoveredBySmallerCandidates r h t target := by
  rfl

private theorem M_le_q_mul_M {r h t q : Nat} (hq : 1 <= q) :
    M r h t <= q * M r h t := by
  have hmul : 1 * M r h t <= q * M r h t :=
    Nat.mul_le_mul_right (M r h t) hq
  simpa using hmul

theorem periodic_block_ge_M {r h t q n : Nat}
    (hq : 1 <= q) (hn : InPeriodicBlock r h t q n) :
    M r h t <= n := by
  rcases hn with ⟨u, _hu, hshift⟩
  have hMle := M_le_q_mul_M (r := r) (h := h) (t := t) hq
  omega

theorem inQ_one_le_D {r h t u : Nat}
    (hp : Params r h t) (hu : InQ r h t 1 u) :
    u <= D r h t := by
  unfold InQ at hu
  rcases hu with hfull | hterm
  · rcases hfull with ⟨i, hiFull⟩
    have hi : i < r := hiFull.1
    have huhi : u <= 2 * i * h + h - 1 := hiFull.2.2
    have hrun_lt :
        2 * i * h + h - 1 < 2 * r * h :=
      full_run_hi_lt_terminal_cap_lo
        (r := r) (h := h) (t := t) (i := i) hp hi
    unfold D
    omega
  · have huhi : u <= 2 * r * h + t := by
      unfold InTerminalCap InInterval at hterm
      exact hterm.2
    simpa [D] using huhi

theorem inE_bounds {r h t n : Nat}
    (hp : Params r h t) (hn : InE r h t n) :
    D r h t <= n ∧ n <= 2 * D r h t + 1 := by
  unfold InE Shift at hn
  rcases hn with ⟨u, hu, hshift⟩
  have huhi := inQ_zero_le_D_add_one (r := r) (h := h) (t := t) hp hu
  constructor <;> omega

theorem inE_lower {r h t n : Nat}
    (hp : Params r h t) (hn : InE r h t n) :
    D r h t <= n :=
  (inE_bounds (r := r) (h := h) (t := t) hp hn).1

theorem inE_upper {r h t n : Nat}
    (hp : Params r h t) (hn : InE r h t n) :
    n <= 2 * D r h t + 1 :=
  (inE_bounds (r := r) (h := h) (t := t) hp hn).2

theorem inF_bounds {r h t n : Nat}
    (hp : Params r h t) (hn : InF r h t n) :
    6 * D r h t + 1 <= n ∧ n <= 7 * D r h t + 1 := by
  unfold InF Shift at hn
  rcases hn with ⟨x, hx, hshiftF⟩
  unfold InX Shift at hx
  rcases hx with ⟨u, hu, hshiftX⟩
  have huhi := inQ_one_le_D (r := r) (h := h) (t := t) hp hu
  constructor <;> omega

theorem inF_lower {r h t n : Nat}
    (hp : Params r h t) (hn : InF r h t n) :
    6 * D r h t + 1 <= n :=
  (inF_bounds (r := r) (h := h) (t := t) hp hn).1

theorem inF_upper {r h t n : Nat}
    (hp : Params r h t) (hn : InF r h t n) :
    n <= 7 * D r h t + 1 :=
  (inF_bounds (r := r) (h := h) (t := t) hp hn).2

theorem inE_lt_minF {r h t n : Nat}
    (hp : Params r h t) (hn : InE r h t n) :
    n < 6 * D r h t + 1 := by
  have hhi := inE_upper (r := r) (h := h) (t := t) hp hn
  have hD := D_ge_three (r := r) (h := h) (t := t) hp
  omega

theorem inF_lt_M {r h t n : Nat}
    (hp : Params r h t) (hn : InF r h t n) :
    n < M r h t := by
  have hhi := inF_upper (r := r) (h := h) (t := t) hp hn
  have hD := D_ge_three (r := r) (h := h) (t := t) hp
  unfold M
  omega

theorem candidate_lt_M_cases {r h t n : Nat}
    (hn : Candidate r h t n) (hnlt : n < M r h t) :
    n = 1 ∨ n = h - 1 ∨ InE r h t n ∨ InF r h t n := by
  unfold Candidate at hn
  rcases hn with h1 | hh | hE | hF | hper
  · exact Or.inl h1
  · exact Or.inr (Or.inl hh)
  · exact Or.inr (Or.inr (Or.inl hE))
  · exact Or.inr (Or.inr (Or.inr hF))
  · rcases hper with ⟨q, hq, hblock⟩
    have hMle := periodic_block_ge_M (r := r) (h := h) (t := t)
      (q := q) (n := n) hq hblock
    omega

theorem candidate_ge_one {r h t n : Nat}
    (hp : Params r h t) (hn : Candidate r h t n) :
    1 <= n := by
  unfold Candidate at hn
  rcases hn with rfl | rfl | hE | hF | hper
  · omega
  · have hh := hp.h_ge_six
    omega
  · have hlo := inE_lower (r := r) (h := h) (t := t) hp hE
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega
  · have hlo := inF_lower (r := r) (h := h) (t := t) hp hF
    omega
  · rcases hper with ⟨q, hq, hblock⟩
    have hMle := periodic_block_ge_M (r := r) (h := h) (t := t)
      (q := q) (n := n) hq hblock
    have hMpos := M_pos (r := r) (h := h) (t := t)
    omega

theorem h_le_D {r h t : Nat}
    (hp : Params r h t) :
    h <= D r h t := by
  have hr := hp.r_pos
  have hcoef : 1 <= 2 * r := by omega
  have hmul : 1 * h <= 2 * r * h :=
    Nat.mul_le_mul_right h hcoef
  unfold D
  omega

theorem h_sub_one_le_twoD_add_one {r h t : Nat}
    (hp : Params r h t) :
    h - 1 <= 2 * D r h t + 1 := by
  have hle := h_le_D (r := r) (h := h) (t := t) hp
  omega

theorem h_sub_one_lt_D {r h t : Nat}
    (hp : Params r h t) :
    h - 1 < D r h t := by
  have hle := h_le_D (r := r) (h := h) (t := t) hp
  have hh := hp.h_ge_six
  omega

theorem candidate_lt_M_notF_le_E_top {r h t n : Nat}
    (hp : Params r h t) (hn : Candidate r h t n)
    (hnlt : n < M r h t) (hnF : ¬ InF r h t n) :
    n <= 2 * D r h t + 1 := by
  rcases candidate_lt_M_cases (r := r) (h := h) (t := t) hn hnlt with
    rfl | rfl | hE | hF
  · have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega
  · exact h_sub_one_le_twoD_add_one (r := r) (h := h) (t := t) hp
  · exact inE_upper (r := r) (h := h) (t := t) hp hE
  · exact False.elim (hnF hF)

theorem ordered_triple_sum_le_sixD_of_top_notF {r h t x y z : Nat}
    (hp : Params r h t)
    (hx : Candidate r h t x) (hy : Candidate r h t y)
    (hz : Candidate r h t z)
    (hxlt : x < M r h t) (hylt : y < M r h t)
    (hzlt : z < M r h t)
    (hxy : x < y) (hyz : y < z) (hzF : ¬ InF r h t z) :
    x + y + z <= 6 * D r h t := by
  have hzle := candidate_lt_M_notF_le_E_top
    (r := r) (h := h) (t := t) hp hz hzlt hzF
  have hyF : ¬ InF r h t y := by
    intro hyF
    have hylo := inF_lower (r := r) (h := h) (t := t) hp hyF
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega
  have hxF : ¬ InF r h t x := by
    intro hxF
    have hxlo := inF_lower (r := r) (h := h) (t := t) hp hxF
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega
  have hyle := candidate_lt_M_notF_le_E_top
    (r := r) (h := h) (t := t) hp hy hylt hyF
  have hxle := candidate_lt_M_notF_le_E_top
    (r := r) (h := h) (t := t) hp hx hxlt hxF
  omega

private theorem full_run_h_shift_not_full_run {r h t i j u v : Nat}
    (hp : Params r h t)
    (_hi : i < r) (_hj : j < r)
    (hu : InInterval (2 * i * h) (2 * i * h + h - 1) u)
    (hv : InInterval (2 * j * h) (2 * j * h + h - 1) v)
    (hshift : v = u + h) :
    False := by
  by_cases hij : i < j
  · have hij_succ : i + 1 <= j := by omega
    have hcoef : 2 * (i + 1) <= 2 * j := by omega
    have hprod : 2 * (i + 1) * h <= 2 * j * h :=
      Nat.mul_le_mul_right h hcoef
    have hprod_eq : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
      rw [Nat.left_distrib, Nat.right_distrib]
    rw [hprod_eq] at hprod
    have hvlo : 2 * j * h <= v := hv.1
    have huhi : u <= 2 * i * h + h - 1 := hu.2
    have hpos : 1 <= h := by
      have hh := hp.h_ge_six
      omega
    have hstep : u + h < 2 * i * h + 2 * h := by omega
    omega
  · have hji : j <= i := by omega
    have hcoef : 2 * j <= 2 * i := by omega
    have hprod : 2 * j * h <= 2 * i * h :=
      Nat.mul_le_mul_right h hcoef
    have hulo : 2 * i * h <= u := hu.1
    have hvhi : v <= 2 * j * h + h - 1 := hv.2
    have hpos : 1 <= h := by
      have hh := hp.h_ge_six
      omega
    have hstep : 2 * i * h + h <= u + h := by omega
    have hhi : 2 * j * h + h - 1 < 2 * i * h + h := by omega
    omega

private theorem full_run_h_shift_not_terminal {r h t s i u v : Nat}
    (hp : Params r h t)
    (hi : i < r)
    (hu : InInterval (2 * i * h) (2 * i * h + h - 1) u)
    (hv : InInterval (2 * r * h) (2 * r * h + t + 1 - s) v)
    (hshift : v = u + h) :
    False := by
  have hi_succ : i + 1 <= r := by omega
  have hcoef : 2 * (i + 1) <= 2 * r := by omega
  have hprod : 2 * (i + 1) * h <= 2 * r * h :=
    Nat.mul_le_mul_right h hcoef
  have hprod_eq : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
    rw [Nat.left_distrib, Nat.right_distrib]
  rw [hprod_eq] at hprod
  have huhi : u <= 2 * i * h + h - 1 := hu.2
  have hvlo : 2 * r * h <= v := hv.1
  have hpos : 1 <= h := by
    have hh := hp.h_ge_six
    omega
  have hstep : u + h < 2 * i * h + 2 * h := by omega
  omega

private theorem terminal_h_shift_not_full_run {r h t s j u v : Nat}
    (hp : Params r h t)
    (hj : j < r)
    (hu : InInterval (2 * r * h) (2 * r * h + t + 1 - s) u)
    (hv : InInterval (2 * j * h) (2 * j * h + h - 1) v)
    (hshift : v = u + h) :
    False := by
  have hgap := full_run_hi_lt_terminal_cap_lo
    (r := r) (h := h) (t := t) (i := j) hp hj
  have hulo : 2 * r * h <= u := hu.1
  have hvhi : v <= 2 * j * h + h - 1 := hv.2
  omega

private theorem terminal_h_shift_not_terminal_of_s_le_one
    {r h t s u v : Nat}
    (hp : Params r h t) (hs : s <= 1)
    (hu : InInterval (2 * r * h) (2 * r * h + t + 1 - s) u)
    (hv : InInterval (2 * r * h) (2 * r * h + t + 1 - s) v)
    (hshift : v = u + h) :
    False := by
  have hh := hp.h_ge_six
  have ht := hp.dense_upper
  have hulo : 2 * r * h <= u := hu.1
  have hvhi : v <= 2 * r * h + t + 1 - s := hv.2
  have ht_s : t + 1 - s <= h - 1 := by omega
  omega

theorem inQ_no_h_shift_of_s_le_one {r h t s u v : Nat}
    (hp : Params r h t) (hs : s <= 1)
    (hu : InQ r h t s u) (hv : InQ r h t s v)
    (hshift : v = u + h) :
    False := by
  unfold InQ at hu hv
  rcases hu with hfullU | htermU
  · rcases hfullU with ⟨i, hi, huI⟩
    rcases hv with hfullV | htermV
    · rcases hfullV with ⟨j, hj, hvI⟩
      exact full_run_h_shift_not_full_run
        (r := r) (h := h) (t := t) (i := i) (j := j)
        (u := u) (v := v) hp hi hj huI hvI hshift
    · exact full_run_h_shift_not_terminal
        (r := r) (h := h) (t := t) (s := s) (i := i)
        (u := u) (v := v) hp hi huI htermV hshift
  · rcases hv with hfullV | htermV
    · rcases hfullV with ⟨j, hj, hvI⟩
      exact terminal_h_shift_not_full_run
        (r := r) (h := h) (t := t) (s := s) (j := j)
        (u := u) (v := v) hp hj htermU hvI hshift
    · exact terminal_h_shift_not_terminal_of_s_le_one
        (r := r) (h := h) (t := t) (s := s)
        (u := u) (v := v) hp hs htermU htermV hshift

theorem inE_no_h_shift {r h t u v : Nat}
    (hp : Params r h t)
    (hu : InE r h t u) (hv : InE r h t v)
    (hshift : v = u + h) :
    False := by
  unfold InE Shift at hu hv
  rcases hu with ⟨u0, hu0, huEq⟩
  rcases hv with ⟨v0, hv0, hvEq⟩
  have hshift0 : v0 = u0 + h := by omega
  exact inQ_no_h_shift_of_s_le_one
    (r := r) (h := h) (t := t) (s := 0)
    (u := u0) (v := v0) hp (by omega) hu0 hv0 hshift0

theorem inF_no_h_shift {r h t u v : Nat}
    (hp : Params r h t)
    (hu : InF r h t u) (hv : InF r h t v)
    (hshift : v = u + h) :
    False := by
  unfold InF Shift at hu hv
  rcases hu with ⟨ux, huX, huEq⟩
  rcases hv with ⟨vx, hvX, hvEq⟩
  unfold InX Shift at huX hvX
  rcases huX with ⟨u0, hu0, huXEq⟩
  rcases hvX with ⟨v0, hv0, hvXEq⟩
  have hshift0 : v0 = u0 + h := by omega
  exact inQ_no_h_shift_of_s_le_one
    (r := r) (h := h) (t := t) (s := 1)
    (u := u0) (v := v0) hp (by omega) hu0 hv0 hshift0

theorem inE_candidateTripleSumFrom_false {r h t target : Nat}
    (hp : Params r h t) (htE : InE r h t target) :
    ¬ CandidateTripleSumFrom r h t target := by
  intro htriple
  rcases htriple with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum⟩
  have htltF := inE_lt_minF (r := r) (h := h) (t := t) hp htE
  have htltM : target < M r h t := by
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    unfold M
    omega
  have hxltM : x < M r h t := by omega
  have hyltM : y < M r h t := by omega
  have hzltM : z < M r h t := by omega
  by_cases hy_small : y <= h - 1
  · have hx_eq_one : x = 1 := by
      rcases candidate_lt_M_cases (r := r) (h := h) (t := t) hx hxltM with
        rfl | rfl | hxE | hxF
      · rfl
      · omega
      · have hxlo := inE_lower (r := r) (h := h) (t := t) hp hxE
        have hD := h_sub_one_lt_D (r := r) (h := h) (t := t) hp
        omega
      · have hxlo := inF_lower (r := r) (h := h) (t := t) hp hxF
        have hD := D_ge_three (r := r) (h := h) (t := t) hp
        omega
    have hy_eq_h : y = h - 1 := by
      rcases candidate_lt_M_cases (r := r) (h := h) (t := t) hy hyltM with
        hy1 | hyh | hyE | hyF
      · rw [hy1] at hxy
        have hxpos := candidate_ge_one (r := r) (h := h) (t := t) hp hx
        omega
      · exact hyh
      · have hylo := inE_lower (r := r) (h := h) (t := t) hp hyE
        have hD := h_sub_one_lt_D (r := r) (h := h) (t := t) hp
        omega
      · have hylo := inF_lower (r := r) (h := h) (t := t) hp hyF
        have hD := D_ge_three (r := r) (h := h) (t := t) hp
        omega
    have hzE : InE r h t z := by
      rcases candidate_lt_M_cases (r := r) (h := h) (t := t) hz hzltM with
        hz1 | hzh | hzE | hzF
      · rw [hz1] at hyz
        have hh := hp.h_ge_six
        omega
      · rw [hzh] at hyz
        omega
      · exact hzE
      · have hzlo := inF_lower (r := r) (h := h) (t := t) hp hzF
        omega
    have htarget_shift : target = z + h := by
      rw [hx_eq_one, hy_eq_h] at hsum
      have hh := hp.h_ge_six
      omega
    exact inE_no_h_shift
      (r := r) (h := h) (t := t) (u := z) (v := target)
      hp hzE htE htarget_shift
  · have hy_large : h - 1 < y := by omega
    have hyE : InE r h t y := by
      rcases candidate_lt_M_cases (r := r) (h := h) (t := t) hy hyltM with
        hy1 | hyh | hyE | hyF
      · rw [hy1] at hy_large
        have hh := hp.h_ge_six
        omega
      · rw [hyh] at hy_large
        omega
      · exact hyE
      · have hylo := inF_lower (r := r) (h := h) (t := t) hp hyF
        omega
    have hzE : InE r h t z := by
      rcases candidate_lt_M_cases (r := r) (h := h) (t := t) hz hzltM with
        hz1 | hzh | hzE | hzF
      · rw [hz1] at hyz
        have hh := hp.h_ge_six
        omega
      · rw [hzh] at hyz
        omega
      · exact hzE
      · have hzlo := inF_lower (r := r) (h := h) (t := t) hp hzF
        omega
    have hxpos := candidate_ge_one (r := r) (h := h) (t := t) hp hx
    have hylo := inE_lower (r := r) (h := h) (t := t) hp hyE
    have hzlo0 := inE_lower (r := r) (h := h) (t := t) hp hzE
    have htarget_hi := inE_upper (r := r) (h := h) (t := t) hp htE
    omega

theorem inF_candidateTripleSumFrom_false {r h t target : Nat}
    (hp : Params r h t) (htF : InF r h t target) :
    ¬ CandidateTripleSumFrom r h t target := by
  intro htriple
  rcases htriple with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum⟩
  have htlo := inF_lower (r := r) (h := h) (t := t) hp htF
  have hthi := inF_upper (r := r) (h := h) (t := t) hp htF
  have htltM := inF_lt_M (r := r) (h := h) (t := t) hp htF
  have hxltM : x < M r h t := by omega
  have hyltM : y < M r h t := by omega
  have hzltM : z < M r h t := by omega
  by_cases hzF : InF r h t z
  · by_cases hy_small : y <= h - 1
    · have hx_eq_one : x = 1 := by
        rcases candidate_lt_M_cases (r := r) (h := h) (t := t) hx hxltM with
          rfl | rfl | hxE | hxF
        · rfl
        · omega
        · have hxlo := inE_lower (r := r) (h := h) (t := t) hp hxE
          have hD := h_sub_one_lt_D (r := r) (h := h) (t := t) hp
          omega
        · have hxlo := inF_lower (r := r) (h := h) (t := t) hp hxF
          have hD := D_ge_three (r := r) (h := h) (t := t) hp
          omega
      have hy_eq_h : y = h - 1 := by
        rcases candidate_lt_M_cases (r := r) (h := h) (t := t) hy hyltM with
          hy1 | hyh | hyE | hyF
        · rw [hy1] at hxy
          have hxpos := candidate_ge_one (r := r) (h := h) (t := t) hp hx
          omega
        · exact hyh
        · have hylo := inE_lower (r := r) (h := h) (t := t) hp hyE
          have hD := h_sub_one_lt_D (r := r) (h := h) (t := t) hp
          omega
        · have hylo := inF_lower (r := r) (h := h) (t := t) hp hyF
          have hD := D_ge_three (r := r) (h := h) (t := t) hp
          omega
      have htarget_shift : target = z + h := by
        rw [hx_eq_one, hy_eq_h] at hsum
        have hh := hp.h_ge_six
        omega
      exact inF_no_h_shift
        (r := r) (h := h) (t := t) (u := z) (v := target)
        hp hzF htF htarget_shift
    · have hy_large : h - 1 < y := by omega
      rcases candidate_lt_M_cases (r := r) (h := h) (t := t) hy hyltM with
        hy1 | hyh | hyE | hyF
      · rw [hy1] at hy_large
        have hh := hp.h_ge_six
        omega
      · rw [hyh] at hy_large
        omega
      · have hxpos := candidate_ge_one (r := r) (h := h) (t := t) hp hx
        have hylo := inE_lower (r := r) (h := h) (t := t) hp hyE
        have hzlo := inF_lower (r := r) (h := h) (t := t) hp hzF
        omega
      · have hxpos := candidate_ge_one (r := r) (h := h) (t := t) hp hx
        have hylo := inF_lower (r := r) (h := h) (t := t) hp hyF
        have hzlo := inF_lower (r := r) (h := h) (t := t) hp hzF
        omega
  · have hsum_le := ordered_triple_sum_le_sixD_of_top_notF
      (r := r) (h := h) (t := t) (x := x) (y := y) (z := z)
      hp hx hy hz hxltM hyltM hzltM hxy hyz hzF
    omega

end TransitionDenseCap
end GreedyThreeSumfree
