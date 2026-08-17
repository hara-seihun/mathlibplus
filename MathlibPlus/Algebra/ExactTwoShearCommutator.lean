import Mathlib

namespace MathlibPlus.Algebra

def upperShear {R : Type*} [CommRing R] (a : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, a; 0, 1]

def lowerShear {R : Type*} [CommRing R] (b : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; b, 1]

def exactTwoShearCommutator : Prop :=
  ∀ {R : Type*} [CommRing R] (a b : R),
    upperShear a * lowerShear b * (upperShear a)⁻¹ * (lowerShear b)⁻¹ =
      !![1 + a * b + a ^ 2 * b ^ 2, -(a ^ 2 * b); a * b ^ 2, 1 - a * b]

end MathlibPlus.Algebra
