import MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1254_30644
import MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1254_30649

namespace MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1254

noncomputable section

abbrev ScalarBase30639 := RepairBase30649 3
abbrev ScalarFiber30639 := RepairFiber30649 1

/-- Embed a normalized scalar function in the one-dimensional fibre carrier
used in the paired-motion formulation. -/
def scalarLift30639
    (u : RepairScalarSpace_30644) : ScalarBase30639 → ScalarFiber30639 :=
  fun x => ![repairScalarValue30644 u x]

def pairedAnnihilator30639
    (u : RepairScalarSpace_30644)
    (x : RepairBase30649 3) : Prop :=
  repairScalarValue30644 u 0 = 0 ∧
    ∀ v : ScalarFiber30639,
      v ∈ repairPairedMotion30649 (scalarLift30639 u) x →
        v 0 = 0

/-- Claim 30639: on each reviewed projective direction, the additive kernel
of the normalized scalar function is exactly the annihilator of the paired
translated second-difference motions in the two inverse directions. -/
def claim30639 : Prop :=
  ∀ i : Fin 13, ∀ u : RepairScalarSpace_30644,
    repairKernelCondition30644 (repairCubeDirection30644 i) u ↔
      pairedAnnihilator30639 u (repairCubeDirection30644 i)

end
end MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1254
