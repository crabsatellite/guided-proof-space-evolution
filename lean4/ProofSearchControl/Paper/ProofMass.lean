import ProofSearchControl.Paper.Definitions

open Filter Topology

namespace ProofSearchControl.Paper

/-- Accepted proof mass is bounded by the proposal protocol's total mass. -/
theorem proofMass_le_one
    (T : MachineCheckableSystem) (φ : Target) (π : ProposalProtocol) :
    proofMass T φ π ≤ 1 := by
  calc
    proofMass T φ π ≤ ∑' p : ProofCode, π p := by
      apply ENNReal.tsum_le_tsum
      intro p
      split <;> simp
    _ = 1 := PMF.tsum_coe π

/-- Paper Proposition `prop:hitting`: tail-sum expectation for repeated attempts. -/
theorem expectedAttempts_eq_tsum_failureTail
    {M : ℝ} (hMpos : 0 < M) (hMle : M ≤ 1) :
    (∑' n : ℕ, failureTail M n) = expectedAttempts M := by
  rw [show (∑' n : ℕ, failureTail M n) = (1 - (1 - M))⁻¹ by
    exact tsum_geometric_of_lt_one (sub_nonneg.mpr hMle) (sub_lt_self 1 hMpos)]
  simp [expectedAttempts]

/-- The geometric failure tail converges to zero on every positive proof mass. -/
theorem failureTail_tendsto_zero
    {M : ℝ} (hMpos : 0 < M) (hMle : M ≤ 1) :
    Tendsto (failureTail M) atTop (nhds 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (sub_nonneg.mpr hMle) (sub_lt_self 1 hMpos)

/-- Exponential upper bound on the independent-attempt failure tail. -/
theorem failureTail_le_exp
    {M : ℝ} (_hMnonneg : 0 ≤ M) (hMle : M ≤ 1) (n : ℕ) :
    failureTail M n ≤ Real.exp (-(n : ℝ) * M) := by
  have hbase_nonneg : 0 ≤ 1 - M := sub_nonneg.mpr hMle
  have hbase : 1 - M ≤ Real.exp (-M) := by
    nlinarith [Real.add_one_le_exp (-M)]
  have hpow : (1 - M) ^ n ≤ (Real.exp (-M)) ^ n := by
    exact pow_le_pow_left₀ hbase_nonneg hbase n
  calc
    failureTail M n = (1 - M) ^ n := rfl
    _ ≤ (Real.exp (-M)) ^ n := hpow
    _ = Real.exp (-(n : ℝ) * M) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Paper Proposition `prop:cost-hitting`, reduced to its exact conditional-cost identity. -/
theorem costAwareHittingLaw
    {M successCost failureCost : ℝ} (hM : M ≠ 0) :
    successCost + ((1 - M) / M) * failureCost =
      (M * successCost + (1 - M) * failureCost) / M := by
  field_simp

/-- Paper Corollary `cor:guidance`: expected-attempt ratios are inverse mass ratios. -/
theorem expectedAttempts_ratio
    {oldMass newMass : ℝ} :
    expectedAttempts oldMass / expectedAttempts newMass = newMass / oldMass := by
  simp [expectedAttempts, div_eq_mul_inv, mul_comm]

/-- The exponential of guidance gain is exactly the proof-mass ratio. -/
theorem exp_guidanceGain
    {oldMass newMass : ℝ} (hold : 0 < oldMass) (hnew : 0 < newMass) :
    Real.exp (guidanceGain oldMass newMass) = newMass / oldMass := by
  exact Real.exp_log (div_pos hnew hold)

/-- Combined multiplicative guidance law from the paper. -/
theorem multiplicativeGuidanceLaw
    {oldMass newMass : ℝ} (hold : 0 < oldMass) (hnew : 0 < newMass) :
    expectedAttempts oldMass / expectedAttempts newMass =
      Real.exp (guidanceGain oldMass newMass) := by
  rw [expectedAttempts_ratio, exp_guidanceGain hold hnew]

end ProofSearchControl.Paper
