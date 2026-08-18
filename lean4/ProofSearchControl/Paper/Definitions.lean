import ProofSearchControl.Basic

open scoped ENNReal

namespace ProofSearchControl.Paper

abbrev Target := ℕ
abbrev ProofCode := ℕ

/-- Paper Definition `def:machine-checkable`: a target-indexed Boolean verifier. -/
structure MachineCheckableSystem where
  verify : ProofCode → Target → Bool

/-- A target is provable exactly when some finite code is accepted. -/
def Provable (T : MachineCheckableSystem) (φ : Target) : Prop :=
  ∃ p : ProofCode, T.verify p φ = true

/-- Paper Definition `def:proof-radius`, on the positive-instance domain. -/
noncomputable def proofRadius
    (T : MachineCheckableSystem) (φ : Target) (h : Provable T φ) : ℕ :=
  Nat.find h

/-- Number of strings of length at most `radius` over an alphabet of size `b`. -/
def candidateStringCount (b radius : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (radius + 1), b ^ k

/-- A proposal protocol is a probability mass function on complete finite outputs. -/
abbrev ProposalProtocol := PMF ProofCode

/-- Paper Definition `def:proof-mass`: total proposal mass on accepted codes. -/
noncomputable def proofMass
    (T : MachineCheckableSystem) (φ : Target) (π : ProposalProtocol) : ℝ≥0∞ :=
  ∑' p : ProofCode, if T.verify p φ then π p else 0

/-- Real-valued proof mass used by the paper's search-distance formulas. -/
noncomputable def proofMassReal
    (T : MachineCheckableSystem) (φ : Target) (π : ProposalProtocol) : ℝ :=
  (proofMass T φ π).toReal

/-- Paper Definition `def:proof-mass`: negative log of total accepted mass. -/
noncomputable def policyRelativeDistance
    (T : MachineCheckableSystem) (φ : Target) (π : ProposalProtocol) : ℝ :=
  -Real.log (proofMassReal T φ π)

/-- Scalar expected-attempt accounting used after a proof mass is fixed. -/
noncomputable def expectedAttempts (M : ℝ) : ℝ := M⁻¹

/-- Log proof-mass improvement from an old protocol to a new protocol. -/
noncomputable def guidanceGain (oldMass newMass : ℝ) : ℝ :=
  Real.log (newMass / oldMass)

/-- Failure probability after `n` independent attempts of mass `M`. -/
def failureTail (M : ℝ) (n : ℕ) : ℝ := (1 - M) ^ n

/-- A fair baseline gives every provable target strictly positive proof mass. -/
def SupportComplete
    (T : MachineCheckableSystem) (πf : Target → ProposalProtocol) : Prop :=
  ∀ φ, Provable T φ → 0 < proofMassReal T φ (πf φ)

/-- Mixture of a guided proof mass and a fair-lane proof mass. -/
def mixedMass (ε guided fair : ℝ) : ℝ :=
  (1 - ε) * guided + ε * fair

/-- Paper Definition `def:and-response`: one edge's homogeneous attempt response. -/
def edgeSuccess (q : ℝ) (n : ℕ) : ℝ :=
  1 - q ^ n

/-- Paper Definition `def:and-response`: a two-edge AND slice with remainder `R`. -/
def andRouteResponse (R q : ℝ) (a b : ℕ) : ℝ :=
  R * edgeSuccess q a * edgeSuccess q b

/-- A typed hyperedge: all inputs jointly produce one output. -/
structure ClaimEdge (Claim : Type*) where
  inputs : Finset Claim
  output : Claim
  deriving DecidableEq

/-- Paper Definition `def:earned-graph`: only listed edges are earned. -/
structure EarnedClaimGraph (Claim : Type*) [DecidableEq Claim] where
  roots : Finset Claim
  earnedEdges : Finset (ClaimEdge Claim)

/-- One monotone reachability step through earned hyperedges. -/
def reachStep {Claim : Type*} [DecidableEq Claim]
    (G : EarnedClaimGraph Claim) (current : Finset Claim) : Finset Claim :=
  current ∪ (G.earnedEdges.filter (fun e ↦ e.inputs ⊆ current)).image ClaimEdge.output

/-- Claims reachable after at most `n` earned-edge composition rounds. -/
def reachableAt {Claim : Type*} [DecidableEq Claim]
    (G : EarnedClaimGraph Claim) : ℕ → Finset Claim
  | 0 => G.roots
  | n + 1 => reachStep G (reachableAt G n)

/-- Unbounded earned reachability is finite-stage membership. -/
def Reachable {Claim : Type*} [DecidableEq Claim]
    (G : EarnedClaimGraph Claim) (claim : Claim) : Prop :=
  ∃ n, claim ∈ reachableAt G n

/-- Paper Definition `def:control-action`: one schedulable research action. -/
structure SearchControlAction
    (TargetId Claim Route Tool Boundary : Type*) where
  target : TargetId
  edge : ClaimEdge Claim
  route : Route
  tool : Tool
  boundary : Boundary

/-- A budget-indexed belief that an action will earn its edge. -/
structure BudgetedClosureBelief where
  probability : ℕ → ℝ
  nonnegative : ∀ B, 0 ≤ probability B
  atMostOne : ∀ B, probability B ≤ 1

/-- Paper's closure-aware myopic allocation index. -/
noncomputable def allocationIndex
    (estimatedReachabilityGain closureWithinBudget expectedTotalCost
      explorationBonus : ℝ) : ℝ :=
  estimatedReachabilityGain * closureWithinBudget / expectedTotalCost +
    explorationBonus

/-- Portfolio objective: expected earned reachability utility minus total cost. -/
def portfolioObjective (expectedUtility expectedTotalCost penalty : ℝ) : ℝ :=
  expectedUtility - penalty * expectedTotalCost

/-- Paper's graph-level verification and composition cost decomposition. -/
def totalEvidenceCost (generation verification transport composition : ℝ) : ℝ :=
  generation + verification + transport + composition

end ProofSearchControl.Paper
