import MathlibPlus.Open.Research.QuaternionBatch

namespace MathlibPlus.Open.Research.R1060Claim32933

open MathlibPlus.Open.Research.QuaternionBatch

noncomputable section

abbrev DegreeTwentyFiber (p : ℕ) := (ZMod p × ZMod 5) × Fin 4

private def inverseLayer (i : Fin 4) : Fin 4 := -i

private def degreeTwentyMul (p : ℕ)
    (a b : DegreeTwentyFiber p) : DegreeTwentyFiber p :=
  ((a.1.1 + chi p a.2 * b.1.1,
      a.1.2 + chi 5 a.2 * b.1.2),
    addFour a.2 b.2)

private def degreeTwentyInverse (p : ℕ)
    (a : DegreeTwentyFiber p) : DegreeTwentyFiber p :=
  ((-((chi p a.2)⁻¹) * a.1.1,
      -((chi 5 a.2)⁻¹) * a.1.2),
    inverseLayer a.2)

private def degreeTwentyBaseSwitch (y : ZMod 5) (i : Fin 4) : ZMod 5 × Fin 4 :=
  ((2 : ZMod 5) ^ i.val * y, i)

private def normalizedDegreeTwentyAffineLift (p : ℕ)
    (f : Equiv.Perm (DegreeTwentyFiber p)) : Prop :=
  ∃ (lam : (ZMod 5 × Fin 4) → (ZMod p)ˣ)
    (tau : (ZMod 5 × Fin 4) → ZMod p),
    lam ((0 : ZMod 5), (0 : Fin 4)) = 1 ∧
      tau ((0 : ZMod 5), (0 : Fin 4)) = 0 ∧
      ∀ (x : ZMod p) (y : ZMod 5) (i : Fin 4),
        f ((x, y), i) =
          (((lam (y, i) : ZMod p) * x + tau (y, i),
              (degreeTwentyBaseSwitch y i).1),
            (degreeTwentyBaseSwitch y i).2)

private def transportedRelativeDerivative (p : ℕ)
    (f : Equiv.Perm (DegreeTwentyFiber p))
    (g x : DegreeTwentyFiber p) : DegreeTwentyFiber p :=
  f.symm
    (degreeTwentyMul p
      (f (degreeTwentyMul p x g))
      (degreeTwentyInverse p (f g)))

private def identityFree (p : ℕ)
    (S : Set (DegreeTwentyFiber p)) : Prop :=
  ((0, 0), 0) ∉ S

private def inverseClosed (p : ℕ)
    (S : Set (DegreeTwentyFiber p)) : Prop :=
  ∀ x : DegreeTwentyFiber p,
    x ∈ S ↔ degreeTwentyInverse p x ∈ S

private def derivativeInvariant (p : ℕ)
    (f : Equiv.Perm (DegreeTwentyFiber p))
    (S : Set (DegreeTwentyFiber p)) : Prop :=
  ∀ g : DegreeTwentyFiber p,
    Set.image (transportedRelativeDerivative p f g) S = S

private def degreeTwentyAutomorphism (p : ℕ)
    (α : Equiv.Perm (DegreeTwentyFiber p)) : Prop :=
  ∀ x y : DegreeTwentyFiber p,
    α (degreeTwentyMul p x y) =
      degreeTwentyMul p (α x) (α y)

/-- Every normalized affine lift of the simultaneous-inversion quartic switch
on `(F_p^+ × F_5^+) ⋊ C₄` has one ordinary-CI automorphism shadow on each
identity-free inverse-closed derivative-invariant connection set. -/
def claim32933_degreeTwentyQuarticSwitchLiftOrdinaryCIHarmless : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) → 5 < p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ f : Equiv.Perm (DegreeTwentyFiber p),
      normalizedDegreeTwentyAffineLift p f →
        ∀ S : Set (DegreeTwentyFiber p),
          identityFree p S →
            inverseClosed p S →
              derivativeInvariant p f S →
                ∃ α : Equiv.Perm (DegreeTwentyFiber p),
                  degreeTwentyAutomorphism p α ∧
                    Set.image f S = Set.image α S

end

end MathlibPlus.Open.Research.R1060Claim32933
