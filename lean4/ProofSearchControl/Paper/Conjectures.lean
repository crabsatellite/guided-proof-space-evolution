import ProofSearchControl.Paper.Definitions

namespace ProofSearchControl.Paper

/-!
The paper's final three claims are explicitly empirical conjectures, not
kernel theorems. They are recorded as stable text declarations so the paper map
can require their presence without introducing an axiom or pretending to prove
an empirical regularity in Lean.
-/

def guidanceGainCalibrationConjecture : String :=
  "Holding verifier and attempt protocol fixed, lower estimated policy-relative proof distance predicts multiplicatively lower realized candidate count, subject to reported dependence, truncation, and cost heterogeneity."

def graphAwarePortfolioGainConjecture : String :=
  "At equal total compute, scheduling by expected earned reachability gain closes more weighted portfolio targets than independent theorem scheduling when targets share load-bearing producers."

def engineeringComplementarityConjecture : String :=
  "The marginal return from stronger LLM guidance is larger when candidate outputs have predeclared verification boundaries, semantic interfaces, and claim-graph consumers."

end ProofSearchControl.Paper
