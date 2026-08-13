import Mathlib.Data.ZMod.Basic

namespace MathlibPlus.Open.GraphTheory

/--
For the cyclic composition of six cubic coordinate shears on `𝔽₅⁶`, the
relative derivative at `e₀`, together with negation, acts transitively on all
nonzero differences. This is the exact obstruction found in the Q-0139
cyclic-feedback attempt.
-/
def cyclicSixCubicShearRelativeDerivativeTransitive : Prop :=
  let V := Fin 6 → ZMod 5
  let shear (source target : Fin 6) (sign : ZMod 5) (x : V) : V :=
    Function.update x target (x target + sign * (x source) ^ 3)
  let q (x : V) : V :=
    shear 5 0 1
      (shear 4 5 1
        (shear 3 4 1
          (shear 2 3 1
            (shear 1 2 1
              (shear 0 1 1 x)))))
  let qInv (x : V) : V :=
    shear 0 1 (-1)
      (shear 1 2 (-1)
        (shear 2 3 (-1)
          (shear 3 4 (-1)
            (shear 4 5 (-1)
              (shear 5 0 (-1) x)))))
  let e₀ : V := fun i => if i = 0 then 1 else 0
  let step (a b : V) : Prop :=
    b = -a ∨ b = qInv (q (e₀ + a) - q e₀)
  ∀ a b : V, a ≠ 0 → b ≠ 0 → Relation.ReflTransGen step a b

end MathlibPlus.Open.GraphTheory
