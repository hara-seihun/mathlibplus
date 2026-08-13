import Mathlib

namespace MathlibPlus.Algebra.Claim10927

/-- The reflection doublet for the zero-weight packet.  The only property of
`Λ` used here is the completed zeta reflection law; the source leaves this law
implicit in the displayed identities. -/
theorem exactZeroWeightReflectionDoublet
    (Λ : ℂ → ℂ) (hΛ : ∀ s : ℂ, Λ (1 - s) = Λ s) :
    let Zplus : ℂ → ℂ := fun s => Λ s * Λ (2 * s)
    let Zminus : ℂ → ℂ := fun s => Λ s * Λ (2 * s - 1)
    (∀ s : ℂ, Zplus (1 - s) = Zminus s) ∧
      (∀ s : ℂ, Zminus (1 - s) = Zplus s) := by
  dsimp
  constructor
  · intro s
    have hsecond : Λ (2 * (1 - s)) = Λ (2 * s - 1) := by
      calc
        Λ (2 * (1 - s)) = Λ (1 - (2 * s - 1)) := by
          congr 1 <;> ring
        _ = Λ (2 * s - 1) := hΛ _
    rw [hΛ s, hsecond]
  · intro s
    have hsecond : Λ (2 * (1 - s) - 1) = Λ (2 * s) := by
      calc
        Λ (2 * (1 - s) - 1) = Λ (1 - 2 * s) := by
          congr 1 <;> ring
        _ = Λ (2 * s) := hΛ _
    rw [hΛ s, hsecond]

end MathlibPlus.Algebra.Claim10927
