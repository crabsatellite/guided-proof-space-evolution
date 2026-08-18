import ProofSearchControl.Paper.Definitions

namespace ProofSearchControl.Paper

variable {Claim : Type*} [DecidableEq Claim]

/-- Every already reachable claim remains reachable after one closure step. -/
theorem subset_reachStep (G : EarnedClaimGraph Claim) (current : Finset Claim) :
    current ⊆ reachStep G current := by
  intro claim hclaim
  exact Finset.mem_union_left _ hclaim

/-- Finite-stage earned reachability is monotone in the number of rounds. -/
theorem reachableAt_subset_succ (G : EarnedClaimGraph Claim) (n : ℕ) :
    reachableAt G n ⊆ reachableAt G (n + 1) := by
  simpa [reachableAt] using subset_reachStep G (reachableAt G n)

/-- Every declared root is reachable at stage zero. -/
theorem root_reachable (G : EarnedClaimGraph Claim) {claim : Claim}
    (hclaim : claim ∈ G.roots) : Reachable G claim := by
  exact ⟨0, hclaim⟩

/-- An earned edge whose inputs are available propagates its output in one round. -/
theorem earnedEdge_output_reachableAt_succ
    (G : EarnedClaimGraph Claim) (n : ℕ) (e : ClaimEdge Claim)
    (he : e ∈ G.earnedEdges) (hinputs : e.inputs ⊆ reachableAt G n) :
    e.output ∈ reachableAt G (n + 1) := by
  simp only [reachableAt, reachStep]
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr
    ⟨e, Finset.mem_filter.mpr ⟨he, hinputs⟩, rfl⟩

/-- Graph-level derived closure: reachable earned inputs license the output claim. -/
theorem earnedEdge_preserves_Reachable
    (G : EarnedClaimGraph Claim) (e : ClaimEdge Claim)
    (he : e ∈ G.earnedEdges)
    (hinputs : ∃ n, e.inputs ⊆ reachableAt G n) :
    Reachable G e.output := by
  obtain ⟨n, hn⟩ := hinputs
  exact ⟨n + 1, earnedEdge_output_reachableAt_succ G n e he hn⟩

end ProofSearchControl.Paper
