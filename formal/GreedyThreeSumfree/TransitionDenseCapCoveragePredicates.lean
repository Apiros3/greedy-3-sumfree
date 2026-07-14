import GreedyThreeSumfree.TransitionDenseCapDistinctTriple

namespace GreedyThreeSumfree
namespace TransitionDenseCap

/--
`target` is covered by three distinct smaller dense-cap candidates.
The strict ordering packages distinctness.
-/
def CoveredBySmallerCandidates (r h t target : Nat) : Prop :=
  ∃ x y z : Nat,
    Candidate r h t x ∧
    Candidate r h t y ∧
    Candidate r h t z ∧
    x < y ∧
    y < z ∧
    z < target ∧
    x + y + z = target

/-- Ordered triple of dense-cap candidates. -/
def OrderedCandidateTriple (r h t x y z : Nat) : Prop :=
  Candidate r h t x ∧
    Candidate r h t y ∧
    Candidate r h t z ∧
    x < y ∧
    y < z

/-- Ordered three-sum from the dense-cap candidate set. -/
def OrderedCandidateTripleSum (r h t n : Nat) : Prop :=
  ∃ x y z : Nat,
    Candidate r h t x ∧
    Candidate r h t y ∧
    Candidate r h t z ∧
    x < y ∧
    y < z ∧
    x + y + z = n

/-- Pointwise candidate coverage by an ordered candidate three-sum. -/
def CandidateTripleCoverage (r h t n : Nat) : Prop :=
  Candidate r h t n ∧ OrderedCandidateTripleSum r h t n

theorem orderedCandidateTripleSum_mk {r h t x y z n : Nat}
    (hx : Candidate r h t x) (hy : Candidate r h t y)
    (hz : Candidate r h t z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = n) :
    OrderedCandidateTripleSum r h t n := by
  exact ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩

theorem inE_of_inQ_zero {r h t u : Nat} (hu : InQ r h t 0 u) :
    InE r h t (D r h t + u) := by
  unfold InE Shift
  exact ⟨u, hu, rfl⟩

theorem inX_of_inQ_one {r h t u : Nat} (hu : InQ r h t 1 u) :
    InX r h t (D r h t + u) := by
  unfold InX Shift
  exact ⟨u, hu, rfl⟩

theorem inW_of_inQ_two {r h t u : Nat} (hu : InQ r h t 2 u) :
    InW r h t (D r h t + u) := by
  unfold InW Shift
  exact ⟨u, hu, rfl⟩

theorem inF_of_inX {r h t u : Nat} (hu : InX r h t u) :
    InF r h t (5 * D r h t + 1 + u) := by
  unfold InF Shift
  exact ⟨u, hu, rfl⟩

theorem inY_of_inW {r h t u : Nat} (hu : InW r h t u) :
    InY r h t (5 * D r h t + 2 + u) := by
  unfold InY Shift
  exact ⟨u, hu, rfl⟩

theorem inTailResidue_of_inX {r h t u : Nat} (hu : InX r h t u) :
    InTailResidue r h t u := by
  unfold InTailResidue
  exact Or.inl hu

theorem inTailResidue_of_inY {r h t u : Nat} (hu : InY r h t u) :
    InTailResidue r h t u := by
  unfold InTailResidue
  exact Or.inr hu

theorem inPeriodicBlock_of_inTailResidue {r h t q u : Nat}
    (hu : InTailResidue r h t u) :
    InPeriodicBlock r h t q (q * M r h t + u) := by
  unfold InPeriodicBlock Shift
  exact ⟨u, hu, rfl⟩

theorem inPeriodicBlock_of_inX {r h t q u : Nat} (hu : InX r h t u) :
    InPeriodicBlock r h t q (q * M r h t + u) := by
  exact inPeriodicBlock_of_inTailResidue (q := q) (inTailResidue_of_inX hu)

theorem inPeriodicBlock_of_inY {r h t q u : Nat} (hu : InY r h t u) :
    InPeriodicBlock r h t q (q * M r h t + u) := by
  exact inPeriodicBlock_of_inTailResidue (q := q) (inTailResidue_of_inY hu)

theorem candidate_of_inE {r h t n : Nat} (hn : InE r h t n) :
    Candidate r h t n := by
  unfold Candidate
  exact Or.inr (Or.inr (Or.inl hn))

theorem inE_candidate {r h t n : Nat} (hn : InE r h t n) :
    Candidate r h t n := by
  exact candidate_of_inE hn

theorem candidate_of_inF {r h t n : Nat} (hn : InF r h t n) :
    Candidate r h t n := by
  unfold Candidate
  exact Or.inr (Or.inr (Or.inr (Or.inl hn)))

theorem inQ_zero_of_inQ_one {r h t u : Nat} (hu : InQ r h t 1 u) :
    InQ r h t 0 u := by
  unfold InQ at hu ⊢
  rcases hu with hfull | hterm
  · exact Or.inl hfull
  · exact Or.inr (by
      unfold InTerminalCap InInterval at hterm ⊢
      omega)

theorem inQ_one_of_inQ_two {r h t u : Nat} (hu : InQ r h t 2 u) :
    InQ r h t 1 u := by
  unfold InQ at hu ⊢
  rcases hu with hfull | hterm
  · exact Or.inl hfull
  · exact Or.inr (by
      unfold InTerminalCap InInterval at hterm ⊢
      omega)

theorem inE_of_inX {r h t n : Nat} (hn : InX r h t n) :
    InE r h t n := by
  unfold InX Shift at hn
  unfold InE Shift
  rcases hn with ⟨u, hu, hshift⟩
  exact ⟨u, inQ_zero_of_inQ_one hu, hshift⟩

theorem inX_of_inW {r h t n : Nat} (hn : InW r h t n) :
    InX r h t n := by
  unfold InW Shift at hn
  unfold InX Shift
  rcases hn with ⟨u, hu, hshift⟩
  exact ⟨u, inQ_one_of_inQ_two hu, hshift⟩

theorem candidate_of_inX {r h t n : Nat} (hn : InX r h t n) :
    Candidate r h t n := by
  exact candidate_of_inE (inE_of_inX hn)

theorem candidate_of_periodic_inTailResidue {r h t q u : Nat}
    (hq : 1 <= q) (hu : InTailResidue r h t u) :
    Candidate r h t (q * M r h t + u) := by
  unfold Candidate
  exact
    Or.inr
      (Or.inr
        (Or.inr
          (Or.inr
            ⟨q, hq, inPeriodicBlock_of_inTailResidue (q := q) hu⟩)))

theorem candidate_of_periodic_inX {r h t q u : Nat}
    (hq : 1 <= q) (hu : InX r h t u) :
    Candidate r h t (q * M r h t + u) := by
  exact candidate_of_periodic_inTailResidue hq (inTailResidue_of_inX hu)

theorem candidate_of_periodic_inY {r h t q u : Nat}
    (hq : 1 <= q) (hu : InY r h t u) :
    Candidate r h t (q * M r h t + u) := by
  exact candidate_of_periodic_inTailResidue hq (inTailResidue_of_inY hu)

theorem candidate_of_inQ_zero_shift {r h t u : Nat}
    (hu : InQ r h t 0 u) :
    Candidate r h t (D r h t + u) := by
  exact candidate_of_inE (inE_of_inQ_zero hu)

theorem D_add_inE_of_inQ {r h t u : Nat} (hu : InQ r h t 0 u) :
    InE r h t (D r h t + u) := by
  exact inE_of_inQ_zero hu

theorem candidate_of_inQ_one_shift {r h t u : Nat}
    (hu : InQ r h t 1 u) :
    Candidate r h t (D r h t + u) := by
  exact candidate_of_inX (inX_of_inQ_one hu)

theorem candidate_of_inX_high_shift {r h t u : Nat}
    (hu : InX r h t u) :
    Candidate r h t (5 * D r h t + 1 + u) := by
  exact candidate_of_inF (inF_of_inX hu)

theorem candidate_of_periodic_inX_shift_one {r h t u : Nat}
    (hu : InX r h t u) :
    Candidate r h t (M r h t + u) := by
  simpa using candidate_of_periodic_inX (q := 1) (r := r) (h := h) (t := t)
    (u := u) (by omega) hu

theorem candidate_of_periodic_inY_shift_one {r h t u : Nat}
    (hu : InY r h t u) :
    Candidate r h t (M r h t + u) := by
  simpa using candidate_of_periodic_inY (q := 1) (r := r) (h := h) (t := t)
    (u := u) (by omega) hu

theorem orderedCandidateTripleSum_of_restrictedThreeQ0Sum_shift_E
    {r h t n : Nat} (hn : RestrictedThreeQ0Sum r h t n) :
    OrderedCandidateTripleSum r h t (3 * D r h t + n) := by
  rcases hn with ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  refine
    orderedCandidateTripleSum_mk
      (x := D r h t + x) (y := D r h t + y) (z := D r h t + z)
      ?_ ?_ ?_ ?_ ?_ ?_
  · exact candidate_of_inQ_zero_shift hx
  · exact candidate_of_inQ_zero_shift hy
  · exact candidate_of_inQ_zero_shift hz
  · omega
  · omega
  · omega

theorem orderedCandidateTriple_left_lt_target {x y z n : Nat}
    (_hxy : x < y) (hyz : y < z) (hsum : x + y + z = n) :
    x < n := by
  omega

theorem orderedCandidateTriple_middle_lt_target {x y z n : Nat}
    (_hxy : x < y) (hyz : y < z) (hsum : x + y + z = n) :
    y < n := by
  omega

theorem orderedCandidateTriple_right_lt_target {x y z n : Nat}
    (hxy : x < y) (_hyz : y < z) (hsum : x + y + z = n) :
    z < n := by
  omega

theorem orderedCandidateTripleSum_witnesses_lt_target {r h t n : Nat}
    (hn : OrderedCandidateTripleSum r h t n) :
    ∃ x y z : Nat,
      Candidate r h t x ∧
        Candidate r h t y ∧
        Candidate r h t z ∧
        x < y ∧
        y < z ∧
        x < n ∧
        y < n ∧
        z < n ∧
        x + y + z = n := by
  rcases hn with ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  exact
    ⟨x, y, z, hx, hy, hz, hxy, hyz,
      orderedCandidateTriple_left_lt_target hxy hyz hsum,
      orderedCandidateTriple_middle_lt_target hxy hyz hsum,
      orderedCandidateTriple_right_lt_target hxy hyz hsum,
      hsum⟩

theorem three_le_target_of_orderedCandidateTripleSum {r h t n : Nat}
    (hn : OrderedCandidateTripleSum r h t n) :
    3 <= n := by
  rcases hn with ⟨x, y, z, _hx, _hy, _hz, hxy, hyz, hsum⟩
  omega

end TransitionDenseCap
end GreedyThreeSumfree
