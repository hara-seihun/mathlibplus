import MathlibPlus.LinearAlgebra.Claim4834

namespace MathlibPlus.Open.LinearAlgebra.Claim4835

noncomputable section

abbrev Profile := ℕ →₀ ℕ

def edge (i : ℕ) (m : Profile) : Profile :=
  m + Finsupp.single i 1

def normalizedH {K : Type*} [Field K]
    (Δ V : Profile → K) (m : {m // V m ≠ 0}) : K :=
  MathlibPlus.LinearAlgebra.Claim4834.normalizedConfluentPluckerCoordinate Δ V m

def edgeConnection {K : Type*} [Field K]
    (ω : ℕ → Profile → K) (Δ V : Profile → K) : Prop :=
  ∀ (i : ℕ) (m : {m // V m ≠ 0}) (h_edge : V (edge i m) ≠ 0),
    normalizedH Δ V m ≠ 0 →
      ω i m =
        normalizedH Δ V ⟨edge i m, h_edge⟩ /
          normalizedH Δ V m

end

end MathlibPlus.Open.LinearAlgebra.Claim4835
