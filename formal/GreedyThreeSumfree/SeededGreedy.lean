import Std

namespace GreedyThreeSumfree

/--
`z` is forbidden by a sum of three distinct smaller elements of a candidate set.
The strict ordering packages distinctness.
-/
def TripleSumFrom (A : Nat → Prop) (z : Nat) : Prop :=
  ∃ x y w : Nat, A x ∧ A y ∧ A w ∧ x < y ∧ y < w ∧ w < z ∧ x + y + w = z

/-- A value is admissible for the next greedy step when no earlier triple sums to it. -/
def GreedyAdmissible (A : Nat → Prop) (z : Nat) : Prop :=
  ¬ TripleSumFrom A z

/-- Recursive step predicate for a greedy set. -/
def RecursiveGreedyStep (A : Nat → Prop) (z : Nat) : Prop :=
  A z ↔ GreedyAdmissible A z

/--
A seeded greedy set agrees with the seed through `threshold` and then follows
the recursive admissibility criterion at every later value.
-/
def SeededGreedySet (seed A : Nat → Prop) (threshold : Nat) : Prop :=
  (∀ z, z <= threshold → (A z ↔ seed z)) ∧
    ∀ z, threshold < z → RecursiveGreedyStep A z

/--
Triple sums only inspect selected values below the target, so two sets that
agree below `z` have the same triple-sum obstruction at `z`.
-/
theorem tripleSumFrom_congr_below {A B : Nat → Prop} {z : Nat}
    (h : ∀ n, n < z → (A n ↔ B n)) :
    TripleSumFrom A z ↔ TripleSumFrom B z := by
  constructor
  · intro ht
    rcases ht with ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩
    refine ⟨x, y, w, ?_, ?_, ?_, hxy, hyw, hwz, hsum⟩
    · exact (h x (by omega)).1 hx
    · exact (h y (by omega)).1 hy
    · exact (h w hwz).1 hw
  · intro ht
    rcases ht with ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩
    refine ⟨x, y, w, ?_, ?_, ?_, hxy, hyw, hwz, hsum⟩
    · exact (h x (by omega)).2 hx
    · exact (h y (by omega)).2 hy
    · exact (h w hwz).2 hw

/--
The seeded recursive criterion determines at most one set: below the current
target use the induction hypothesis, and at the target use congruence of the
triple obstruction.
-/
theorem seededGreedySet_ext {seed A B : Nat → Prop} {threshold : Nat}
    (hA : SeededGreedySet seed A threshold)
    (hB : SeededGreedySet seed B threshold) :
    ∀ z, A z ↔ B z := by
  intro z
  exact Nat.strongRecOn z (motive := fun n => A n ↔ B n) (fun z ih => by
    by_cases hzle : z <= threshold
    · exact Iff.trans (hA.1 z hzle) (Iff.symm (hB.1 z hzle))
    · have hzgt : threshold < z := by omega
      have hstepA : RecursiveGreedyStep A z := hA.2 z hzgt
      have hstepB : RecursiveGreedyStep B z := hB.2 z hzgt
      have htriple : TripleSumFrom A z ↔ TripleSumFrom B z :=
        tripleSumFrom_congr_below ih
      have hadm : GreedyAdmissible A z ↔ GreedyAdmissible B z := by
        unfold GreedyAdmissible
        constructor
        · intro hnot htb
          exact hnot (htriple.mpr htb)
        · intro hnot hta
          exact hnot (htriple.mp hta)
      exact Iff.trans hstepA (Iff.trans hadm (Iff.symm hstepB)))

end GreedyThreeSumfree
