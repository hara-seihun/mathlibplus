import MathlibPlus.Open.ResearchFormalization.R1108Claim30020
import MathlibPlus.Open.ResearchFormalization.R0992Claim28041

namespace MathlibPlus.Open.ResearchFormalization.R1108R1135PeriodicTables

noncomputable section

open Classical
open MathlibPlus.Open.ResearchFormalization.R0992Claim28041

private def basis0 :
    MathlibPlus.Open.ResearchFormalization.R1108.Plane :=
  fun i => if i = 0 then 1 else 0

private def basis1 :
    MathlibPlus.Open.ResearchFormalization.R1108.Plane :=
  fun i => if i = 1 then 1 else 0

private def lineRepresentative : Fin 4 →
    MathlibPlus.Open.ResearchFormalization.R1108.Plane
  | 0 => basis0
  | 1 => basis1
  | 2 => basis0 + basis1
  | 3 => basis0 - basis1

private def lineSubmodule
    (v : MathlibPlus.Open.ResearchFormalization.R1108.Plane) :
    Submodule (ZMod 3)
      MathlibPlus.Open.ResearchFormalization.R1108.Plane :=
  Submodule.span (ZMod 3) ({v} : Set _)

private def rankTwoPeriodicResidualTable
    (D : MathlibPlus.Open.ResearchFormalization.R1108.Plane →
      MathlibPlus.Open.ResearchFormalization.R1108.Codomain) : Prop :=
  D 0 = 0 ∧
    (∃ t, t ≠ 0 ∧ ∀ x, D (x + t) = D x) ∧
    ∃ j : Fin 4,
      ∃ φ :
          (MathlibPlus.Open.ResearchFormalization.R1108.Plane ⧸
              lineSubmodule (lineRepresentative j)) →
            MathlibPlus.Open.ResearchFormalization.R1108.Codomain,
        (∀ x, D x = φ (Submodule.Quotient.mk x)) ∧
          ∃ u w,
            u ≠ 0 ∧ w ≠ 0 ∧ u ≠ w ∧
              LinearIndependent (ZMod 3) ![φ u, φ w]

private noncomputable def rankTwoPeriodicResidualTables :
    Finset
      (MathlibPlus.Open.ResearchFormalization.R1108.Plane →
        MathlibPlus.Open.ResearchFormalization.R1108.Codomain) :=
  (Finset.univ.filter rankTwoPeriodicResidualTable)

/-- Claim 30021: the normalized rank-two periodic residual-table carrier has
exactly four period lines, a nonzero first quotient value, an independent
second quotient value, and the exact count `4(27-1)(27-3)=2496`. -/
def exactPeriodicRankTwoResidualCount_claim30021 : Prop :=
  Nat.card {
      L : Submodule (ZMod 3)
        (MathlibPlus.Open.ResearchFormalization.R1108.Plane) //
        Module.finrank (ZMod 3) L = 1} = 4 ∧
    rankTwoPeriodicResidualTables.card =
      4 * (27 - 1) * (27 - 3) ∧
    rankTwoPeriodicResidualTables.card = 2496

/-- Claim 30108: every normalized nonconstant periodic coefficient table on
`F₃²` has a unique period line and factors through its three-element quotient
with quotient values `0,A,B`, not both zero; the rank-one and rank-two
censuses are exactly 416 and 2496. -/
def normalizedPeriodicNonconstantParametrization_claim30108 : Prop :=
  (∀ F :
      MathlibPlus.Open.ResearchFormalization.R0992Claim28041.Plane →
        MathlibPlus.Open.ResearchFormalization.R0992Claim28041.Output,
    normalizedPeriodicTable F →
      F ≠ 0 →
      ∃! K : Submodule (ZMod 3)
          MathlibPlus.Open.ResearchFormalization.R0992Claim28041.Plane,
        Module.finrank (ZMod 3) K = 1 ∧
          factorsThroughLine F K ∧
          ∃ A B :
              MathlibPlus.Open.ResearchFormalization.R0992Claim28041.Output,
            (A ≠ 0 ∨ B ≠ 0) ∧
              Set.range F ⊆ ({0, A, B} : Set
                MathlibPlus.Open.ResearchFormalization.R0992Claim28041.Output)) ∧
    (rankTables 1).card = 416 ∧
    (rankTables 2).card = 2496 ∧
    4 * (27 ^ 2 - 1) = 2912 ∧
    (rankTables 1).card + (rankTables 2).card = 2912

end

end MathlibPlus.Open.ResearchFormalization.R1108R1135PeriodicTables
