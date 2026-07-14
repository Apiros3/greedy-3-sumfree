import GreedyThreeSumfree.TransitionDenseCapQuotientCarry

namespace GreedyThreeSumfree.TransitionDenseCap

def CandidateResidueDecomposition (r h t n q sigma : Nat) : Prop :=
  n = q * M r h t + sigma ∧
    AllowedResidue r h t sigma ∧
      sigma < M r h t ∧
        (PrefixOnlyResidue r h t sigma → n = sigma)

theorem occupiedTailResidue_allowedResidue {r h t n : Nat}
    (hn : OccupiedTailResidue r h t n) :
    AllowedResidue r h t n := by
  unfold OccupiedTailResidue at hn
  unfold AllowedResidue SigmaResidue
  rcases hn with hx | hy
  · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hy)))

theorem occupiedTailResidue_lt_M {r h t n : Nat}
    (hp : Params r h t) (hn : OccupiedTailResidue r h t n) :
    n < M r h t :=
  allowedResidue_lt_M (r := r) (h := h) (t := t) hp
    (occupiedTailResidue_allowedResidue (r := r) (h := h) (t := t) hn)

theorem candidateResidueDecomposition_of_candidate {r h t n : Nat}
    (hp : Params r h t) (hn : Candidate r h t n) :
    ∃ q sigma : Nat, CandidateResidueDecomposition r h t n q sigma := by
  unfold Candidate at hn
  rcases hn with hsmall1 | hsmallH | hE | hF | hper
  · subst n
    have hallowed : AllowedResidue r h t 1 := by
      unfold AllowedResidue SigmaResidue SmallResidue
      exact Or.inl (Or.inl rfl)
    exact
      ⟨0, 1, by simp, hallowed,
        allowedResidue_lt_M (r := r) (h := h) (t := t) hp hallowed,
        by intro _; rfl⟩
  · subst n
    have hallowed : AllowedResidue r h t (h - 1) := by
      unfold AllowedResidue SigmaResidue SmallResidue
      exact Or.inl (Or.inr rfl)
    exact
      ⟨0, h - 1, by simp, hallowed,
        allowedResidue_lt_M (r := r) (h := h) (t := t) hp hallowed,
        by intro _; rfl⟩
  · have hallowed : AllowedResidue r h t n := by
      unfold AllowedResidue SigmaResidue
      exact Or.inr (Or.inl hE)
    exact
      ⟨0, n, by simp, hallowed,
        allowedResidue_lt_M (r := r) (h := h) (t := t) hp hallowed,
        by intro _; rfl⟩
  · have hallowed : AllowedResidue r h t n := by
      unfold AllowedResidue SigmaResidue
      exact Or.inr (Or.inr (Or.inl hF))
    exact
      ⟨0, n, by simp, hallowed,
        allowedResidue_lt_M (r := r) (h := h) (t := t) hp hallowed,
        by intro _; rfl⟩
  · rcases hper with ⟨q, _hq, hblock⟩
    unfold InPeriodicBlock Shift at hblock
    rcases hblock with ⟨u, huTail, hdecomp⟩
    have hocc : OccupiedTailResidue r h t u := by
      simpa [OccupiedTailResidue, InTailResidue] using huTail
    have hallowed : AllowedResidue r h t u :=
      occupiedTailResidue_allowedResidue (r := r) (h := h) (t := t) hocc
    exact
      ⟨q, u, hdecomp, hallowed,
        allowedResidue_lt_M (r := r) (h := h) (t := t) hp hallowed,
        by
          intro hprefix
          exact False.elim (hprefix.2 hocc)⟩

theorem decomposed_mod_eq {m q sigma n : Nat}
    (hsigma : sigma < m) (hdecomp : n = q * m + sigma) :
    n % m = sigma := by
  rw [hdecomp]
  calc
    (q * m + sigma) % m = (sigma + q * m) % m := by rw [Nat.add_comm]
    _ = sigma % m := by rw [Nat.add_mul_mod_self_right]
    _ = sigma := Nat.mod_eq_of_lt hsigma

theorem decomposed_sum_residue_mod_eq
    {m x y z a b c qx qy qz : Nat}
    (ha : a < m) (hb : b < m) (hc : c < m)
    (hx : x = qx * m + a) (hy : y = qy * m + b)
    (hz : z = qz * m + c) :
    (x + y + z) % m = (a + b + c) % m := by
  have hxmod := decomposed_mod_eq (m := m) (q := qx) (sigma := a) (n := x) ha hx
  have hymod := decomposed_mod_eq (m := m) (q := qy) (sigma := b) (n := y) hb hy
  have hzmod := decomposed_mod_eq (m := m) (q := qz) (sigma := c) (n := z) hc hz
  simp [Nat.add_mod, hxmod, hymod, hzmod]

theorem residue_sum_eq_with_div_carry {m sum rho : Nat}
    (hmod : sum % m = rho) :
    sum = rho + (sum / m) * m := by
  calc
    sum = sum % m + m * (sum / m) := by rw [Nat.mod_add_div]
    _ = rho + m * (sum / m) := by rw [hmod]
    _ = rho + (sum / m) * m := by rw [Nat.mul_comm]

theorem candidateResidueDecomposition_admissible
    {r h t x y z qx qy qz a b c : Nat}
    (hx : CandidateResidueDecomposition r h t x qx a)
    (hy : CandidateResidueDecomposition r h t y qy b)
    (hz : CandidateResidueDecomposition r h t z qz c)
    (hxy : x < y) (hyz : y < z) :
    AdmissibleResidueTriple r h t a b c := by
  refine ⟨hx.2.1, hy.2.1, hz.2.1, ?_⟩
  intro v hv
  constructor
  · intro hxv hyv
    have hxa : x = a := hx.2.2.2 (by simpa [hxv] using hv)
    have hyb : y = b := hy.2.2.2 (by simpa [hyv] using hv)
    omega
  · constructor
    · intro hxv hzv
      have hxa : x = a := hx.2.2.2 (by simpa [hxv] using hv)
      have hzc : z = c := hz.2.2.2 (by simpa [hzv] using hv)
      omega
    · intro hyv hzv
      have hyb : y = b := hy.2.2.2 (by simpa [hyv] using hv)
      have hzc : z = c := hz.2.2.2 (by simpa [hzv] using hv)
      omega

theorem periodic_tail_candidate_safe
    {r h t q rho : Nat} (hp : Params r h t)
    (hq : 1 <= q) (hrho : OccupiedTailResidue r h t rho) :
    ¬ CandidateTripleSumFrom r h t (q * M r h t + rho) := by
  intro htriple
  rcases htriple with ⟨x, y, z, hx, hy, hz, hxy, hyz, _hzlt, hsum⟩
  rcases candidateResidueDecomposition_of_candidate
      (r := r) (h := h) (t := t) hp hx with
    ⟨qx, a, hdx⟩
  rcases candidateResidueDecomposition_of_candidate
      (r := r) (h := h) (t := t) hp hy with
    ⟨qy, b, hdy⟩
  rcases candidateResidueDecomposition_of_candidate
      (r := r) (h := h) (t := t) hp hz with
    ⟨qz, c, hdz⟩
  have hA : AdmissibleResidueTriple r h t a b c :=
    candidateResidueDecomposition_admissible
      (r := r) (h := h) (t := t)
      (x := x) (y := y) (z := z)
      (qx := qx) (qy := qy) (qz := qz)
      (a := a) (b := b) (c := c)
      hdx hdy hdz hxy hyz
  have hrho_lt : rho < M r h t :=
    occupiedTailResidue_lt_M (r := r) (h := h) (t := t) hp hrho
  have hsum_mod :
      (a + b + c) % M r h t = rho := by
    have hleft :
        (x + y + z) % M r h t =
          (a + b + c) % M r h t :=
      decomposed_sum_residue_mod_eq
        (m := M r h t)
        (x := x) (y := y) (z := z)
        (a := a) (b := b) (c := c)
        (qx := qx) (qy := qy) (qz := qz)
        hdx.2.2.1 hdy.2.2.1 hdz.2.2.1
        hdx.1 hdy.1 hdz.1
    have htarget_mod :
        (q * M r h t + rho) % M r h t = rho :=
      decomposed_mod_eq
        (m := M r h t) (q := q) (sigma := rho)
        (n := q * M r h t + rho) hrho_lt rfl
    have htarget_from_sum :
        (x + y + z) % M r h t = (q * M r h t + rho) % M r h t := by
      rw [hsum]
    omega
  let carry := (a + b + c) / M r h t
  have hresidue :
      a + b + c =
        rho + carry * M r h t :=
    residue_sum_eq_with_div_carry
      (m := M r h t)
      (sum := a + b + c)
      (rho := rho) hsum_mod
  have hclass := tail_residue_hit_classification
    (r := r) (h := h) (t := t)
    (rho := rho) (carry := carry)
    (a := a) (b := b) (c := c)
    hp hA hrho hresidue
  rcases hclass.2 with habc | hacb | hbca
  · have hprefix := smallSmallFGapHit_prefixOnlyResidues
      (r := r) (h := h) (t := t) hp habc
    have hx_actual : x = a := hdx.2.2.2 hprefix.1
    have hy_actual : y = b := hdy.2.2.2 hprefix.2.1
    have hz_actual : z = c := hdz.2.2.2 hprefix.2.2
    exact smallSmallFGapHit_decomposed_positive_block_false
      (r := r) (h := h) (t := t) (q := q)
      (q1 := qx) (q2 := qy) (q3 := qz)
      (carry := carry) (rho := rho) (target := q * M r h t + rho)
      (n1 := x) (n2 := y) (n3 := z)
      (sigma1 := a) (sigma2 := b) (sigma3 := c)
      hp hq habc hx hy hz hx_actual hy_actual hz_actual
      hdx.1 hdy.1 hdz.1 rfl hsum hclass.1
  · have hprefix := smallSmallFGapHit_prefixOnlyResidues
      (r := r) (h := h) (t := t) hp hacb
    have hx_actual : x = a := hdx.2.2.2 hprefix.1
    have hz_actual : z = c := hdz.2.2.2 hprefix.2.1
    have hy_actual : y = b := hdy.2.2.2 hprefix.2.2
    exact smallSmallFGapHit_decomposed_positive_block_false
      (r := r) (h := h) (t := t) (q := q)
      (q1 := qx) (q2 := qz) (q3 := qy)
      (carry := carry) (rho := rho) (target := q * M r h t + rho)
      (n1 := x) (n2 := z) (n3 := y)
      (sigma1 := a) (sigma2 := c) (sigma3 := b)
      hp hq hacb hx hz hy hx_actual hz_actual hy_actual
      hdx.1 hdz.1 hdy.1 rfl (by omega) hclass.1
  · have hprefix := smallSmallFGapHit_prefixOnlyResidues
      (r := r) (h := h) (t := t) hp hbca
    have hy_actual : y = b := hdy.2.2.2 hprefix.1
    have hz_actual : z = c := hdz.2.2.2 hprefix.2.1
    have hx_actual : x = a := hdx.2.2.2 hprefix.2.2
    exact smallSmallFGapHit_decomposed_positive_block_false
      (r := r) (h := h) (t := t) (q := q)
      (q1 := qy) (q2 := qz) (q3 := qx)
      (carry := carry) (rho := rho) (target := q * M r h t + rho)
      (n1 := y) (n2 := z) (n3 := x)
      (sigma1 := b) (sigma2 := c) (sigma3 := a)
      hp hq hbca hy hz hx hy_actual hz_actual hx_actual
      hdy.1 hdz.1 hdx.1 rfl (by omega) hclass.1

theorem periodic_tail_coveredBySmallerCandidates_safe
    {r h t q rho : Nat} (hp : Params r h t)
    (hq : 1 <= q) (hrho : OccupiedTailResidue r h t rho) :
    ¬ CoveredBySmallerCandidates r h t (q * M r h t + rho) := by
  simpa [candidateTripleSumFrom_iff_coveredBySmallerCandidates] using
    periodic_tail_candidate_safe
      (r := r) (h := h) (t := t) (q := q) (rho := rho) hp hq hrho

end GreedyThreeSumfree.TransitionDenseCap
