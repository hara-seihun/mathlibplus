import Mathlib

namespace MathlibPlus.Open.Research

abbrev F5 := ZMod 5
abbrev F5Vec3 := Fin 3 → F5
abbrev V := F5Vec3 × F5Vec3

def canonicalFunctional (a : V) : Prop :=
  (∃ i : Fin 3, a.1 i = 1 ∧ ∀ j : Fin 3, j < i → a.1 j = 0) ∨
    (a.1 = 0 ∧ ∃ i : Fin 3, a.2 i = 1 ∧ ∀ j : Fin 3, j < i → a.2 j = 0)

noncomputable def projectiveFunctionals : Finset V := by
  classical
  exact Finset.univ.filter canonicalFunctional

noncomputable def P : Type := (projectiveFunctionals : Finset V)

deriving noncomputable instance Fintype for P

def functionalValue (a x : V) : F5 :=
  (∑ i, a.1 i * x.1 i) + (∑ i, a.2 i * x.2 i)

noncomputable def profile (S : Finset V) : Multiset Nat :=
  (Finset.univ : Finset P).val.map
    (fun a => (S.filter (fun x => functionalValue a.1 x = 0)).card)

def linearImage (e : V ≃ₗ[F5] V) (S : Finset V) : Finset V :=
  S.image e

noncomputable def Claim60674 : Prop :=
  Fintype.card P = 3906 ∧
    (∀ S : Finset V, ∀ e : V ≃ₗ[F5] V,
      profile (linearImage e S) = profile S) ∧
    (∀ S T : Finset V, profile S ≠ profile T →
      ¬ ∃ e : V ≃ₗ[F5] V, linearImage e S = T)

end MathlibPlus.Open.Research
