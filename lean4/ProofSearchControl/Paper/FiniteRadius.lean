import ProofSearchControl.Paper.Definitions

namespace ProofSearchControl.Paper

/-- The shortest code selected by `proofRadius` is accepted. -/
theorem proofRadius_verified
    (T : MachineCheckableSystem) (φ : Target) (h : Provable T φ) :
    T.verify (proofRadius T φ h) φ = true := by
  exact Nat.find_spec h

/-- No smaller code than `proofRadius` is accepted. -/
theorem proofRadius_minimal
    (T : MachineCheckableSystem) (φ : Target) (h : Provable T φ)
    {p : ProofCode} (hp : p < proofRadius T φ h) :
    T.verify p φ = false := by
  have hnot : ¬ T.verify p φ = true := by
    intro hpTrue
    have hle : proofRadius T φ h ≤ p := Nat.find_min' h hpTrue
    exact (Nat.not_le_of_gt hp) hle
  cases hv : T.verify p φ <;> simp_all

/-- Paper Theorem `thm:finite-radius`: closed form for the finite search ball. -/
theorem candidateStringCount_closedForm
    {b radius : ℕ} (hb : 1 < b) :
    (candidateStringCount b radius : ℝ) =
      (((b : ℝ) ^ (radius + 1) - 1) / ((b : ℝ) - 1)) := by
  simp only [candidateStringCount, Nat.cast_sum, Nat.cast_pow]
  exact geom_sum_eq (by exact_mod_cast hb.ne') (radius + 1)

/-- A proposed computable upper bound on accepted proof codes. -/
def UniformCodeBound (T : MachineCheckableSystem) (B : Target → ℕ) : Prop :=
  ∀ φ, Provable T φ → ∃ p ≤ B φ, T.verify p φ = true

/-- Executable bounded proof search through all codes at most `B φ`. -/
def boundedDecision
    (T : MachineCheckableSystem) (B : Target → ℕ) (φ : Target) : Bool :=
  (List.range (B φ + 1)).any (fun p ↦ T.verify p φ)

/-- A Boolean decision procedure with exact positive and negative behavior. -/
structure BooleanDecisionProcedure (T : MachineCheckableSystem) where
  run : Target → Bool
  correct : ∀ φ, run φ = true ↔ Provable T φ

/-- Any effective uniform proof-code bound gives a total Boolean decision procedure. -/
def decisionProcedureOfUniformBound
    (T : MachineCheckableSystem) (B : Target → ℕ) (hB : UniformCodeBound T B) :
    BooleanDecisionProcedure T where
  run := boundedDecision T B
  correct := by
    intro φ
    constructor
    · intro h
      rw [boundedDecision, List.any_eq_true] at h
      obtain ⟨p, hpRange, hpVerify⟩ := h
      exact ⟨p, hpVerify⟩
    · intro h
      obtain ⟨p, hpBound, hpVerify⟩ := hB φ h
      rw [boundedDecision, List.any_eq_true]
      exact ⟨p, by simpa using Nat.lt_succ_iff.mpr hpBound, hpVerify⟩

/-- Paper Proposition `prop:no-bound`, in executable reduction form. -/
theorem no_uniform_bound_of_no_boolean_decider
    (T : MachineCheckableSystem)
    (hUndecidable : ¬ Nonempty (BooleanDecisionProcedure T)) :
    ¬ ∃ B : Target → ℕ, UniformCodeBound T B := by
  rintro ⟨B, hB⟩
  exact hUndecidable ⟨decisionProcedureOfUniformBound T B hB⟩

end ProofSearchControl.Paper
