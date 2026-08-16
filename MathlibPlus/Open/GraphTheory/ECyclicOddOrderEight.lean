import Mathlib

namespace MathlibPlus.Open.GraphTheory.ECyclicOddOrderEight

/-- Coordinates for the semidirect presentation
`E(C_n,8) = ⟨a,b | a^n = b^8 = 1, b⁻¹ab = a⁻¹⟩`. -/
abbrev ECoordinate (n : ℕ) := ZMod n × Fin 8

/-- Addition in the cyclic phase coordinate. -/
def phaseAdd (i j : Fin 8) : Fin 8 :=
  ⟨(i.val + j.val) % 8, Nat.mod_lt _ (by omega)⟩

/-- Multiplication in the displayed `C_n ⋊ C_8` coordinates. -/
def coordinateMul {n : ℕ} (x y : ECoordinate n) : ECoordinate n :=
  (x.1 + (-1 : ZMod n) ^ x.2.val * y.1, phaseAdd x.2 y.2)

/-- The identity coordinate in the displayed presentation. -/
def coordinateOne (n : ℕ) : ECoordinate n :=
  (0, 0)

/-- Powers for the displayed coordinate multiplication. -/
def coordinatePow (n : ℕ) (x : ECoordinate n) : ℕ → ECoordinate n
  | 0 => coordinateOne n
  | k + 1 => coordinateMul (coordinatePow n x k) x

/-- The two presentation generators in coordinates. -/
def generatorA (n : ℕ) : ECoordinate n :=
  (1, 0)

def generatorB (n : ℕ) : ECoordinate n :=
  (0, 1)

/-- The coordinate map induced by `a ↦ a` and `b ↦ b³`. -/
def fixedBCubingMap (n : ℕ) : ECoordinate n → ECoordinate n :=
  fun x => (x.1, ⟨(3 * x.2.val) % 8, Nat.mod_lt _ (by omega)⟩)

/-- A bijective homomorphism for the displayed coordinate group law. -/
def coordinateGroupAutomorphism {n : ℕ}
    (f : ECoordinate n → ECoordinate n) : Prop :=
  Function.Bijective f ∧
    ∀ x y, f (coordinateMul x y) = coordinateMul (f x) (f y)

/-- Exact admitted fixed automorphism: on every odd-order parameter, cubing the
`C_8` coordinate fixes `a` and sends `b` to `b³`. -/
def fixedBCubingAutomorphism : Prop :=
  ∀ n : ℕ, Odd n →
    coordinateGroupAutomorphism (fixedBCubingMap n) ∧
      fixedBCubingMap n (generatorA n) = generatorA n ∧
      fixedBCubingMap n (generatorB n) = coordinatePow n (generatorB n) 3

end MathlibPlus.Open.GraphTheory.ECyclicOddOrderEight
