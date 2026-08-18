import MathlibPlus.Open.ResearchFormalization.R0322Claim19813
import MathlibPlus.Open.ResearchFormalization.R0322Claim19814

namespace MathlibPlus.Open.ResearchFormalization.R0322Claim19820

open scoped BigOperators Classical
open MathlibPlus.Open.ResearchFormalization.R0322Claim19813

noncomputable section

/-- The exact partition carrier cardinality used by the degree table. -/
def partitionCount (k : ℕ) : ℕ :=
  Nat.card (Partition k)

/-- The span of the exact degree-`k` partition carrier. -/
def degreeKSpace (k : ℕ) : Submodule ℚ Sym :=
  letI : Module ℚ Sym := (Algebra.toModule : Module ℚ Sym)
  Submodule.span ℚ (degreeKSpan k)

/-- The algebra map restricted to the exact degree-`k` span. -/
def restrictedGamma (k : ℕ) :=
  letI : Module ℚ Sym := (Algebra.toModule : Module ℚ Sym)
  letI : Module ℚ RationalFunction3 :=
    (Algebra.toModule : Module ℚ RationalFunction3)
  γ.toLinearMap.domRestrict (degreeKSpace k)

/-- The kernel dimension of the restricted degree map. -/
def kernelDimension (k : ℕ) : ℕ :=
  letI : Module ℚ Sym := (Algebra.toModule : Module ℚ Sym)
  letI : Module ℚ RationalFunction3 :=
    (Algebra.toModule : Module ℚ RationalFunction3)
  Module.finrank ℚ (LinearMap.ker (restrictedGamma k))

/-- Claim 19820: the exact partition, rank, and restricted-kernel table for
all degrees from nine through twenty. -/
def claim19820_exactRankKernelTable : Prop :=
  let partitionCounts : Fin 12 → ℕ :=
    ![30, 42, 56, 77, 101, 135, 176, 231, 297, 385, 490, 627]
  let ranks : Fin 12 → ℕ :=
    ![29, 40, 51, 67, 83, 105, 127, 156, 185, 222, 259, 305]
  let kernels : Fin 12 → ℕ :=
    ![1, 2, 5, 10, 18, 30, 49, 75, 112, 163, 231, 322]
  ∀ i : Fin 12,
    let k := i.1 + 9
    partitionCount k = partitionCounts i ∧
      rankGamma k = ranks i ∧
        kernelDimension k = kernels i

end

end MathlibPlus.Open.ResearchFormalization.R0322Claim19820
