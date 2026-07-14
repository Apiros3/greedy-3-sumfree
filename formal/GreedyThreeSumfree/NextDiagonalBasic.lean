import GreedyThreeSumfree.TheoremA

namespace GreedyThreeSumfree
namespace NextDiagonal

/-- Standing hypotheses for the diagonal `S_{1,g,2g+1}` theorem. -/
structure Params (g : Nat) : Prop where
  five_le_g : 5 <= g

def M (g : Nat) : Nat := 8 * g + 5
def c (g : Nat) : Nat := 4 * g + 3
def blockLo (g : Nat) : Nat := 2 * g
def blockHi (g : Nat) : Nat := 3 * g

def InH (g z : Nat) : Prop := InInterval (2 * g + 1) (3 * g + 1) z
def InBlock (g q z : Nat) : Prop :=
  InInterval (q * M g + blockLo g) (q * M g + blockHi g) z

theorem seedTriple_gt_prefix {g z : Nat} (_h : Params g)
    (hz : InInterval (2 * g + 2) (3 * g + 1) z) :
    z < 1 + g + (2 * g + 1) := by
  have hz_upper : z <= 3 * g + 1 := hz.2
  omega

theorem singleton_safe_gap_low (g : Nat) :
    1 + g + (3 * g + 1) = 4 * g + 2 := by
  omega

theorem singleton_safe_gap_high (g : Nat) :
    1 + (2 * g + 1) + (2 * g + 2) = 4 * g + 4 := by
  omega

theorem sameBlockLowerBound_gt_blockEnd (g q : Nat) :
    q * M g + blockHi g < (q * M g + blockLo g) + 1 + g := by
  unfold blockLo blockHi
  omega

theorem sameBlockTerm_exceeds_sameBlockTarget {g q x z : Nat}
    (_h : Params g) (hx : InBlock g q x) (hz : InBlock g q z) :
    z < x + 1 + g := by
  have htop : z <= q * M g + blockHi g := hz.2
  have hbig : q * M g + blockHi g < (q * M g + blockLo g) + 1 + g :=
    sameBlockLowerBound_gt_blockEnd g q
  have hx_lower : q * M g + blockLo g <= x := hx.1
  omega

theorem residue_lower_bound (g : Nat) :
    1 + g + 2 * g = 3 * g + 1 := by
  omega

theorem residue_upper_bound (g : Nat) :
    (4 * g + 3) + (3 * g + 1) + 3 * g = 10 * g + 4 := by
  omega

theorem residue_difference_upper {g r : Nat}
    (hr : InInterval (2 * g) (3 * g) r) :
    (10 * g + 4) - r <= 8 * g + 4 := by
  have hr_lower : 2 * g <= r := hr.1
  omega

theorem prefixSecondGap_overlap_one {g : Nat} (_h : Params g) :
    5 * g + 3 <= 6 * g + 3 := by
  omega

theorem prefixSecondGap_overlap_two {g : Nat} (h : Params g) :
    6 * g + 6 <= 7 * g + 2 := by
  have hg := h.five_le_g
  omega

theorem prefixSecondGap_overlap_three {g : Nat} (h : Params g) :
    8 * g + 6 <= 9 * g + 1 := by
  have hg := h.five_le_g
  omega

theorem periodicGap_overlap_last {g : Nat} (h : Params g) :
    8 * g + 4 <= 9 * g + 2 := by
  have hg := h.five_le_g
  omega

end NextDiagonal

end GreedyThreeSumfree
