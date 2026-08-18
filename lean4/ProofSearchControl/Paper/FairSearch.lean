import ProofSearchControl.Paper.FiniteRadius
import ProofSearchControl.Paper.ProofMass

open Filter Topology

namespace ProofSearchControl.Paper

/-- The fair component is always retained by the mixed proof mass. -/
theorem fairComponent_le_mixedMass
    {ε guided fair : ℝ}
    (hεle : ε ≤ 1) (hguided : 0 ≤ guided) :
    ε * fair ≤ mixedMass ε guided fair := by
  have hweight : 0 ≤ 1 - ε := sub_nonneg.mpr hεle
  have : 0 ≤ (1 - ε) * guided := mul_nonneg hweight hguided
  simp only [mixedMass]
  linarith

/-- A mixture of subprobability masses is again at most one. -/
theorem mixedMass_le_one
    {ε guided fair : ℝ}
    (hεnonneg : 0 ≤ ε) (hεle : ε ≤ 1)
    (hguided : guided ≤ 1) (hfair : fair ≤ 1) :
    mixedMass ε guided fair ≤ 1 := by
  have hweight : 0 ≤ 1 - ε := sub_nonneg.mpr hεle
  have hg : (1 - ε) * guided ≤ (1 - ε) * 1 :=
    mul_le_mul_of_nonneg_left hguided hweight
  have hf : ε * fair ≤ ε * 1 :=
    mul_le_mul_of_nonneg_left hfair hεnonneg
  simp only [mixedMass]
  linarith

/-- Paper Theorem `thm:fair-mixture`: positive fair mass makes mixed mass positive. -/
theorem completenessReserve_positive
    {ε guided fair : ℝ}
    (hεpos : 0 < ε) (hεle : ε ≤ 1)
    (hguided : 0 ≤ guided) (hfair : 0 < fair) :
    0 < mixedMass ε guided fair := by
  have hfairPart : 0 < ε * fair := mul_pos hεpos hfair
  exact hfairPart.trans_le
    (fairComponent_le_mixedMass (fair := fair) hεle hguided)

/-- Explicit expected-attempt overhead of the completeness reserve. -/
theorem completenessReserve_expectedAttempts_le
    {ε guided fair : ℝ}
    (hεpos : 0 < ε) (hεle : ε ≤ 1)
    (hguided : 0 ≤ guided) (hfair : 0 < fair) :
    expectedAttempts (mixedMass ε guided fair) ≤ (ε * fair)⁻¹ := by
  have hfairPart : 0 < ε * fair := mul_pos hεpos hfair
  have hLower := fairComponent_le_mixedMass (fair := fair) hεle hguided
  simpa [expectedAttempts] using one_div_le_one_div_of_le hfairPart hLower

/-- Adaptive-history form of the paper's explicit failure bound. Every
conditional attempt mass may change, but it retains the fair floor. -/
theorem adaptiveFailureProduct_le
    {ε fair : ℝ} (mass : ℕ → ℝ)
    (hfloor : ∀ t, ε * fair ≤ mass t)
    (hmass_le : ∀ t, mass t ≤ 1) (n : ℕ) :
    (∏ t ∈ Finset.range n, (1 - mass t)) ≤ (1 - ε * fair) ^ n := by
  calc
    (∏ t ∈ Finset.range n, (1 - mass t)) ≤
        ∏ _t ∈ Finset.range n, (1 - ε * fair) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact sub_nonneg.mpr (hmass_le i)
      · intro i hi
        exact sub_le_sub_left (hfloor i) 1
    _ = (1 - ε * fair) ^ n := by simp

/-- Almost-sure-discovery content: the mixed failure tail tends to zero. -/
theorem completenessReserve_failureTail_tendsto_zero
    {ε guided fair : ℝ}
    (hεpos : 0 < ε) (hεle : ε ≤ 1)
    (hguided_nonneg : 0 ≤ guided) (hguided_le : guided ≤ 1)
    (hfair_pos : 0 < fair) (hfair_le : fair ≤ 1) :
    Tendsto (failureTail (mixedMass ε guided fair)) atTop (nhds 0) := by
  apply failureTail_tendsto_zero
  · exact completenessReserve_positive hεpos hεle hguided_nonneg hfair_pos
  · exact mixedMass_le_one hεpos.le hεle hguided_le hfair_le

/-- Paper Corollary `cor:reserve-distance`: the fair-lane distance overhead. -/
theorem completenessReserve_distance_le
    {ε guided fair : ℝ}
    (hεpos : 0 < ε) (hεle : ε ≤ 1)
    (hguided : 0 ≤ guided) (hfair : 0 < fair) :
    -Real.log (mixedMass ε guided fair) ≤ -Real.log fair - Real.log ε := by
  have hfairPart : 0 < ε * fair := mul_pos hεpos hfair
  have hLower := fairComponent_le_mixedMass (fair := fair) hεle hguided
  have hlog : Real.log (ε * fair) ≤ Real.log (mixedMass ε guided fair) :=
    Real.log_le_log hfairPart hLower
  calc
    -Real.log (mixedMass ε guided fair) ≤ -Real.log (ε * fair) := neg_le_neg hlog
    _ = -Real.log fair - Real.log ε := by
      rw [Real.log_mul hεpos.ne' hfair.ne']
      ring

/-- Arithmetic core of paper Proposition `prop:dovetail`. -/
theorem deterministicDovetailing_block_count
    {q baselineSteps : ℕ} (hq : 0 < q) :
    (q * baselineSteps) / q = baselineSteps := by
  rw [Nat.mul_comm]
  exact Nat.mul_div_left baselineSteps hq

/-- Abstract finite-portfolio corollary: unbounded cumulative fair work
eventually exceeds every positive target's finite proof radius. -/
theorem portfolio_unbounded_work_reaches_radius
    {ι : Type*} (T : MachineCheckableSystem)
    (target : ι → Target) (work : ℕ → ι → ℕ)
    (hunbounded : ∀ i N, ∃ t, N ≤ work t i) :
    ∀ i (h : Provable T (target i)),
      ∃ t, proofRadius T (target i) h ≤ work t i := by
  intro i h
  exact hunbounded i (proofRadius T (target i) h)

end ProofSearchControl.Paper
