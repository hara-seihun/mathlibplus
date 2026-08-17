import MathlibPlus.Open.Combinatorics.R2667.Claim42272

namespace MathlibPlus.Open.Combinatorics.R2667.Claim42264

abbrev Ground14 :=
  MathlibPlus.Open.Combinatorics.R2667.Claim42272.Ground14
abbrev Family14 :=
  MathlibPlus.Open.Combinatorics.R2667.Claim42272.Family14

/-- The root join `J = R₁ ∪ R₂` in the normalized endpoint setup. -/
def rootJoin14 (R₁ R₂ : Finset Ground14) : Finset Ground14 :=
  R₁ ∪ R₂

/-- The subfamily `D_R = {A ∈ G | A ⊆ R}` generated below a root. -/
def downFamily14 (G : Family14) (R : Finset Ground14) : Family14 :=
  G.filter (fun A => A ⊆ R)

/-- The upper subfamily `K_R = {A ∈ G | R ⊆ A}` generated above a root. -/
def upFamily14 (G : Family14) (R : Finset Ground14) : Family14 :=
  G.filter (fun A => R ⊆ A)

/-- The pairwise-union family `P = {A₁ ∪ A₂ | A₁ ∈ D₁, A₂ ∈ D₂}`. -/
def pairwiseUnionFamily14
    (G : Family14) (R₁ R₂ : Finset Ground14) : Family14 :=
  ((downFamily14 G R₁).product (downFamily14 G R₂)).image
    (fun q => q.1 ∪ q.2)

/-- The coupled generated core `C = P ∪ K₁ ∪ K₂`. -/
def coupledGeneratedFamily14
    (G : Family14) (R₁ R₂ : Finset Ground14) : Family14 :=
  pairwiseUnionFamily14 G R₁ R₂ ∪ upFamily14 G R₁ ∪ upFamily14 G R₂

/-- The residual family `B = G \ C`. -/
def residualGeneratedFamily14
    (G : Family14) (R₁ R₂ : Finset Ground14) : Family14 :=
  G \ coupledGeneratedFamily14 G R₁ R₂

end MathlibPlus.Open.Combinatorics.R2667.Claim42264
