import MathlibPlus.Open.ResearchFormalization.R0913RootedContextChannels

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0913ContextMatrices25582

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0913

/-- The jet contributed by one rooted branch in the reviewed aggregate fold. -/
def branchJet {R : Type*} [CommRing R]
    (branch : MathlibPlus.Open.ResearchFormalization.R0913.RootedTree) : Jet R :=
  ((1 : R), (0 : R), (rootedBranchDegree branch : R))

/-- The matrix obtained by applying the reviewed context action one branch at
 a time from the identity matrix. -/
def branchByBranchAction {R : Type*} [CommRing R]
    (context : MathlibPlus.Open.ResearchFormalization.R0913.RootedContext) : Matrix (Fin 4) (Fin 4) R :=
  context.foldl
    (fun A branch => A * contextActionMatrix (branchJet branch))
    (1 : Matrix (Fin 4) (Fin 4) R)

/-- Claim 25582: context-jet multiplication is represented functorially by
commuting context matrices, and the branch-by-branch rooted assembly equals
one action by the aggregate jet. -/
def claim25582 : Prop :=
  ∀ {R : Type*} [CommRing R] [CharZero R],
    (∀ c c' : Jet R,
      contextActionMatrix (rootJetProduct c c') =
          contextActionMatrix c * contextActionMatrix c' ∧
        contextActionMatrix (rootJetProduct c c') =
          contextActionMatrix c' * contextActionMatrix c) ∧
      ∀ context : MathlibPlus.Open.ResearchFormalization.R0913.RootedContext,
        contextActionMatrix (aggregateJet (R := R) context) =
          branchByBranchAction context

end

end MathlibPlus.Open.ResearchFormalization.R0913ContextMatrices25582
