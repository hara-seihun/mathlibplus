import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

def incidenceIntersectionCount {Ω : Type*} [Fintype Ω]
    {m k : ℕ} (R : Fin m → Set (Ω × Ω))
    (indices : Fin k → Fin m) (points : Fin k → Ω) : ℕ :=
  Set.ncard {z : Ω | ∀ j, (points j, z) ∈ R (indices j)}

def completeIncidenceIntersectionSignature {Ω : Type*} [Fintype Ω]
    (m : ℕ) (R : Fin m → Set (Ω × Ω)) :
    (k : ℕ) → (Fin k → Fin m) → (Fin k → Ω) → ℕ :=
  fun k indices points => incidenceIntersectionCount R indices points

end

end MathlibPlus.Open.ResearchFormalization
