import Mathlib

namespace MathlibPlus
namespace Open

/-- The relative derivative attached to a bijection of a group. -/
def relativeDerivative {G : Type*} [Group G] (f : G ≃ G) (v s : G) : G :=
  f.symm (f (s * v) * (f v)⁻¹)

/-- A subset invariant under all relative derivatives. -/
def derivativeInvariant {G : Type*} [Group G] (f : G ≃ G) (S : Set G) : Prop :=
  ∀ v, relativeDerivative f v '' S = S

/-- Inverse-closure of a subset of a group. -/
def inverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S

/--
Prime-coprime triangular derivative sterility: on the product of the
additive prime field and a coprime finite group, either of the two stated
triangular families sends every derivative-invariant set to itself.
-/
def primeCoprimeTriangularDerivativeSterility : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (K : Type*) [Fintype K] [Group K],
    letI : Fact p.Prime := ⟨hp⟩
    ¬ p ∣ Fintype.card K →
    let G := Multiplicative (ZMod p) × K
    ∀ (f : G ≃ G),
      f (Multiplicative.ofAdd 0, (1 : K)) =
          (Multiplicative.ofAdd 0, (1 : K)) →
      ∀ (S : Set G),
        derivativeInvariant f S →
        ((∃ (lam : K → (ZMod p)ˣ) (t : K → ZMod p),
            lam 1 = 1 ∧
            t 1 = 0 ∧
            ∀ (x : ZMod p) (h : K),
              f (Multiplicative.ofAdd x, h) =
                (Multiplicative.ofAdd
                    (((lam h : (ZMod p)ˣ) : ZMod p) * x + t h), h)) ∨
         (∃ (q : ZMod p → K → K),
            (∀ x, Function.Bijective (q x)) ∧
            (∀ x, q x 1 = 1) ∧
            q 0 = id ∧
            ∀ (x : ZMod p) (h : K),
              f (Multiplicative.ofAdd x, h) =
                (Multiplicative.ofAdd x, q x h))) →
        f '' S = S ∧
          ∀ (T : Set G),
            T = f '' S →
            (1 ∉ S ∧ inverseClosed S ∧ 1 ∉ T ∧ inverseClosed T) →
            T = S

end Open
end MathlibPlus
