import Mathlib

/-!
# No common scalar completion for the three Rankin channels

Registry statement for the reflection obstruction between the Eisenstein and
vacuum channels.
-/

namespace MathlibPlus.Open.NumberTheory.RankinChannels

open Filter Topology

/-- No nonzero meromorphic scalar can simultaneously make the Eisenstein and
vacuum Rankin channels invariant under `s ↦ 1-s`.  Their quotient
`Q(s) = ζ(s-11)ζ(s+11)/ζ(2s)` has a pole at `12`, whereas its reflected value
has the finite limit `-1/4` at `-11`.

The channels are expanded using the coefficient identities
`𝔈 = ζ(s) Z₃(s) / ζ(2s)`, `Z₃(s)=ζ(s-11)ζ(s)ζ(s+11)`, and
`𝔙 = ζ(s)^2`.
-/
def noScalarCompletion : Prop :=
  let Z₃ : ℂ → ℂ := fun s =>
    riemannZeta (s - 11) * riemannZeta s * riemannZeta (s + 11)
  let E : ℂ → ℂ := fun s => riemannZeta s * Z₃ s / riemannZeta (2 * s)
  let V : ℂ → ℂ := fun s => riemannZeta s ^ 2
  let Q : ℂ → ℂ := fun s =>
    riemannZeta (s - 11) * riemannZeta (s + 11) / riemannZeta (2 * s)
  (¬ ∃ M : ℂ → ℂ,
      MeromorphicOn M Set.univ ∧ M ≠ 0 ∧
      (∀ᶠ s in codiscrete ℂ, M (1 - s) * E (1 - s) = M s * E s) ∧
      (∀ᶠ s in codiscrete ℂ, M (1 - s) * V (1 - s) = M s * V s)) ∧
    Tendsto (fun s => (Q s)⁻¹) (𝓝[≠] (12 : ℂ)) (𝓝 0) ∧
    (∀ᶠ s in 𝓝[≠] (12 : ℂ), Q s ≠ 0) ∧
    Tendsto Q (𝓝 (-11 : ℂ)) (𝓝 (-1 / 4 : ℂ))

end MathlibPlus.Open.NumberTheory.RankinChannels
