import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1230
import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb8e2b7983b4fa777bb174bb2d

namespace MathlibPlus.Open.Research.R1230R1253

noncomputable section

open Polynomial
open MathlibPlus.Open.ResearchFormalization.R1230
open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb8e2b7983b4fa777bb174bb2d

def claim30383_centerRootedFactorRigidity : Prop :=
  (∀ (a b a' b' : ℕ),
    admissibleParameter (a, b) →
    admissibleParameter (a', b') →
    spiderFactor a b = spiderFactor a' b' →
      MathlibPlus.Open.ResearchFormalization.R1230.spiderB a b =
          MathlibPlus.Open.ResearchFormalization.R1230.spiderB a' b' ∧
      MathlibPlus.Open.ResearchFormalization.R1230.spiderOrder a b =
          MathlibPlus.Open.ResearchFormalization.R1230.spiderOrder a' b' ∧
      MathlibPlus.Open.ResearchFormalization.R1230.spiderH a b =
          MathlibPlus.Open.ResearchFormalization.R1230.spiderH a' b' ∧
      a = a' ∧ b = b') ∧
  (∀ (a b a' b' : ℕ),
    admissibleParameter (a, b) →
    admissibleParameter (a', b') →
    (a, b) ≠ (a', b') →
    ¬ Associated (spiderFactor a b) (spiderFactor a' b'))

def claim30629_degreeSixNorms : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    Module.finrank ℚ
        (AdjoinRoot (gRat d)) = 6 ∧
      Algebra.norm ℚ (AdjoinRoot.root (gRat d)) = (d - 1 : ℚ) ∧
      Algebra.norm ℚ (1 + AdjoinRoot.root (gRat d)) = (d : ℚ) ∧
      Algebra.norm ℚ
          ((AdjoinRoot.root (gRat d)) ^ 2 +
            AdjoinRoot.root (gRat d) + 1) = (1 : ℚ)

end

end MathlibPlus.Open.Research.R1230R1253
