import ProofSearchControl.Paper.Definitions

namespace ProofSearchControl.Paper

/-- The two conjuncts are symmetric in the AND-route response. -/
theorem andRouteResponse_comm (R q : ℝ) (a b : ℕ) :
    andRouteResponse R q a b = andRouteResponse R q b a := by
  simp only [andRouteResponse]
  ring

/-- Paper Theorem `thm:and-balance-identity`: exact gain from one balancing move. -/
theorem oneUnitBalancingIdentity (R q : ℝ) (a d : ℕ) :
    andRouteResponse R q (a + 1) (a + d + 1) -
      andRouteResponse R q a (a + d + 2) =
        R * q ^ a * (1 - q) * (1 - q ^ (d + 1)) := by
  simp only [andRouteResponse, edgeSuccess]
  rw [show a + d + 1 = a + (d + 1) by omega]
  rw [show a + d + 2 = a + (d + 2) by omega]
  simp only [pow_add, pow_succ]
  ring

/-- Paper Theorem `thm:and-balance-strict`: an underfunded conjunct
strictly benefits from a same-total one-unit transfer. -/
theorem underfundedConjunct_strictlyImproves
    {R q : ℝ} (hR : 0 < R) (hqpos : 0 < q) (hqlt : q < 1)
    (a d : ℕ) :
    andRouteResponse R q a (a + d + 2) <
      andRouteResponse R q (a + 1) (a + d + 1) := by
  apply sub_pos.mp
  rw [oneUnitBalancingIdentity]
  have hqa : 0 < q ^ a := pow_pos hqpos a
  have hqpow : q ^ (d + 1) < 1 :=
    pow_lt_one₀ hqpos.le hqlt (Nat.succ_ne_zero d)
  have hOneQ : 0 < 1 - q := sub_pos.mpr hqlt
  have hOnePow : 0 < 1 - q ^ (d + 1) := sub_pos.mpr hqpow
  exact mul_pos (mul_pos (mul_pos hR hqa) hOneQ) hOnePow

/-- Optimality among all two-edge allocations with the same total budget. -/
def PairOptimal (R q : ℝ) (a b : ℕ) : Prop :=
  ∀ a' b' : ℕ, a' + b' = a + b →
    andRouteResponse R q a' b' ≤ andRouteResponse R q a b

/-- Paper Corollary `cor:and-pairwise-balance`: every optimal homogeneous
two-conjunct allocation differs by at most one attempt. -/
theorem pairOptimal_pairwiseBalanced
    {R q : ℝ} (hR : 0 < R) (hqpos : 0 < q) (hqlt : q < 1)
    {a b : ℕ} (hopt : PairOptimal R q a b) :
    a ≤ b + 1 ∧ b ≤ a + 1 := by
  constructor
  · by_contra hnot
    have hgap : b + 2 ≤ a := by omega
    obtain ⟨d, hd0⟩ := Nat.exists_eq_add_of_le hgap
    have hd : a = b + d + 2 := by omega
    rw [hd] at hopt
    have hsame : (b + 1) + (b + d + 1) = (b + d + 2) + b := by omega
    have hle := hopt (b + 1) (b + d + 1) hsame
    have hstrict := underfundedConjunct_strictlyImproves hR hqpos hqlt b d
    rw [andRouteResponse_comm R q (b + d + 2) b] at hle
    exact (not_lt_of_ge hle) hstrict
  · by_contra hnot
    have hgap : a + 2 ≤ b := by omega
    obtain ⟨d, hd0⟩ := Nat.exists_eq_add_of_le hgap
    have hd : b = a + d + 2 := by omega
    rw [hd] at hopt
    have hsame : (a + 1) + (a + d + 1) = a + (a + d + 2) := by omega
    have hle := hopt (a + 1) (a + d + 1) hsame
    have hstrict := underfundedConjunct_strictlyImproves hR hqpos hqlt a d
    exact (not_lt_of_ge hle) hstrict

end ProofSearchControl.Paper
