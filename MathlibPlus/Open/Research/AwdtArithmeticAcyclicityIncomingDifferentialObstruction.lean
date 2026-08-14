import Mathlib

namespace MathlibPlus
namespace Open
namespace AwdtArithmeticAcyclicity

/-- Exactness at the middle term of a three-term cochain complex of copies of `ℤ`. -/
def exactAtMiddle (d₁ d₂ : ℤ →ₗ[ℤ] ℤ) : Prop :=
  LinearMap.range d₁ = LinearMap.ker d₂

/--
The admitted obstruction claim: the same graded groups and zero outgoing
map support both an exact and a non-exact middle term, with both cochain
conditions holding and with `1` witnessing the non-boundary closed class.
-/
def awdtArithmeticAcyclicityIncomingDifferentialObstruction : Prop :=
  let d₂ : ℤ →ₗ[ℤ] ℤ := 0
  let d₁Exact : ℤ →ₗ[ℤ] ℤ := LinearMap.id
  let d₁Nonexact : ℤ →ₗ[ℤ] ℤ := 0
  d₂.comp d₁Exact = 0 ∧
    d₂.comp d₁Nonexact = 0 ∧
    exactAtMiddle d₁Exact d₂ ∧
    ¬ exactAtMiddle d₁Nonexact d₂ ∧
    d₂ 1 = 0 ∧
    ∀ x : ℤ, d₁Nonexact x ≠ 1

end AwdtArithmeticAcyclicity
end Open
end MathlibPlus
