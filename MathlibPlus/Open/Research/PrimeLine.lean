import Mathlib

namespace MathlibPlus.Open.Research.PrimeLine

abbrev primeLineBase (p m : ℕ) [Fact p.Prime] := Fin m → ZMod p

def normalizedPrimeLineLift
    (p m : ℕ) [Fact p.Prime]
    (g : {g : primeLineBase p m ≃ primeLineBase p m // g 0 = 0})
    (s : {s : primeLineBase p m → ZMod p // s 0 = 0}) :
    ZMod p × primeLineBase p m → ZMod p × primeLineBase p m :=
  fun zh => (zh.1 + s.1 zh.2, g.1 zh.2)

abbrev baseCharacterGroup (p m : ℕ) [Fact p.Prime] :=
  (primeLineBase p m →ₗ[ZMod p] ZMod p)

def scalarFunctionBelongsToBaseCharacterGroupIffAdditive
    (p m : ℕ) [Fact p.Prime]
    (χ : primeLineBase p m → ZMod p) : Prop :=
  (∃ φ : baseCharacterGroup p m, ∀ h, φ.toFun h = χ h) ↔
    ∀ x y, χ (x + y) = χ x + χ y

end MathlibPlus.Open.Research.PrimeLine
