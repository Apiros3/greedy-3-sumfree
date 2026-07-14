import Std

namespace GreedyThreeSumfree

/-- Closed interval membership for natural numbers. -/
def NatInterval (lo hi n : Nat) : Prop := lo <= n ∧ n <= hi

/--
Every target in `[2L+1, 2U-1]` is a sum of two distinct ordered elements of
`[L,U]`, provided the interval has at least two elements.
-/
theorem interval_pair_sum_distinct {L U t : Nat} (hLU : L < U)
    (ht : NatInterval (2 * L + 1) (2 * U - 1) t) :
    ∃ u v : Nat,
      NatInterval L U u ∧ NatInterval L U v ∧ u < v ∧ u + v = t := by
  have htlo : 2 * L + 1 <= t := ht.1
  have hthi : t <= 2 * U - 1 := ht.2
  by_cases hmid : t <= L + U
  · let u := L
    let v := t - L
    have hvlo : L <= v := by
      dsimp [v]
      apply Nat.le_sub_of_add_le
      omega
    have hvhi : v <= U := by
      dsimp [v]
      rw [Nat.sub_le_iff_le_add]
      omega
    have huv : u < v := by
      dsimp [u, v]
      have : L + 1 <= t - L := by
        apply Nat.le_sub_of_add_le
        omega
      omega
    have hsum : u + v = t := by
      dsimp [u, v]
      have hLt : L <= t := by omega
      exact Nat.add_sub_of_le hLt
    refine ⟨u, v, ?_, ?_, huv, hsum⟩
    · dsimp [u, NatInterval]
      constructor <;> omega
    · dsimp [NatInterval]
      exact ⟨hvlo, hvhi⟩
  · let u := t - U
    let v := U
    have hUleT : U <= t := by
      have hgt : L + U < t := by omega
      omega
    have hulo : L <= u := by
      dsimp [u]
      apply Nat.le_sub_of_add_le
      omega
    have huhi : u <= U := by
      dsimp [u]
      rw [Nat.sub_le_iff_le_add]
      omega
    have huv : u < v := by
      dsimp [u, v]
      have hlt : t - U < U := by omega
      exact hlt
    have hsum : u + v = t := by
      dsimp [u, v]
      exact Nat.sub_add_cancel hUleT
    refine ⟨u, v, ?_, ?_, huv, hsum⟩
    · dsimp [NatInterval]
      exact ⟨hulo, huhi⟩
    · dsimp [v, NatInterval]
      constructor <;> omega

/--
Every target in `[3L+3, 3U-3]` is a sum of three distinct ordered elements of
`[L,U]`, provided the interval has at least three elements.
-/
theorem interval_triple_sum_distinct {L U t : Nat} (hwidth : L + 2 <= U)
    (ht : NatInterval (3 * L + 3) (3 * U - 3) t) :
    ∃ u v w : Nat,
      NatInterval L U u ∧
      NatInterval L U v ∧
      NatInterval L U w ∧
      u < v ∧ v < w ∧ u + v + w = t := by
  have htlo : 3 * L + 3 <= t := ht.1
  have hthi : t <= 3 * U - 3 := ht.2
  let G := U - L
  let T := t - 3 * L
  have hLU : L <= U := by omega
  have hU_eq : L + G = U := by
    dsimp [G]
    exact Nat.add_sub_of_le hLU
  have hthiG : t <= 3 * (L + G) - 3 := by
    rw [hU_eq]
    exact hthi
  have hT_eq : 3 * L + T = t := by
    dsimp [T]
    have hle : 3 * L <= t := by omega
    exact Nat.add_sub_of_le hle
  have hGwidth : 2 <= G := by
    dsimp [G]
    omega
  have hTlo : 3 <= T := by
    dsimp [T]
    apply Nat.le_sub_of_add_le
    omega
  have hThi : T <= 3 * G - 3 := by
    dsimp [T]
    rw [Nat.sub_le_iff_le_add]
    omega
  by_cases hcase1 : T <= G + 1
  · let u := L
    let v := L + 1
    let w := L + (T - 1)
    have hTminus : T - 1 <= G := by omega
    have horder : u < v ∧ v < w := by
      dsimp [u, v, w]
      omega
    have hsum : u + v + w = t := by
      dsimp [u, v, w]
      omega
    refine ⟨u, v, w, ?_, ?_, ?_, horder.1, horder.2, hsum⟩
    · dsimp [u, NatInterval]
      constructor <;> omega
    · dsimp [v, NatInterval]
      constructor <;> omega
    · dsimp [w, NatInterval]
      constructor <;> omega
  · by_cases hcase2 : T <= 2 * G - 1
    · let u := L
      let v := L + (T - G)
      let w := L + G
      have hTg_lo : 1 <= T - G := by
        apply Nat.le_sub_of_add_le
        omega
      have hTg_hi : T - G <= G := by
        rw [Nat.sub_le_iff_le_add]
        omega
      have horder : u < v ∧ v < w := by
        dsimp [u, v, w]
        have hlt : T - G < G := by omega
        omega
      have hsum : u + v + w = t := by
        dsimp [u, v, w]
        omega
      refine ⟨u, v, w, ?_, ?_, ?_, horder.1, horder.2, hsum⟩
      · dsimp [u, NatInterval]
        constructor <;> omega
      · dsimp [v, NatInterval]
        constructor <;> omega
      · dsimp [w, NatInterval]
        constructor <;> omega
    · let u := L + (T - (2 * G - 1))
      let v := L + (G - 1)
      let w := L + G
      have hT2g_le_g : T - (2 * G - 1) <= G := by omega
      have hT2g_lt_g_minus : T - (2 * G - 1) < G - 1 := by omega
      have horder : u < v ∧ v < w := by
        dsimp [u, v, w]
        omega
      have hsum : u + v + w = t := by
        dsimp [u, v, w]
        omega
      refine ⟨u, v, w, ?_, ?_, ?_, horder.1, horder.2, hsum⟩
      · dsimp [u, NatInterval]
        constructor <;> omega
      · dsimp [v, NatInterval]
        constructor <;> omega
      · dsimp [w, NatInterval]
        constructor <;> omega

end GreedyThreeSumfree
