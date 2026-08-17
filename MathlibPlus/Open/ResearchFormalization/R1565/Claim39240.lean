import MathlibPlus.Open.ResearchFormalization.R1022

namespace MathlibPlus.Open.ResearchFormalization.R1565.Claim39240

abbrev CTwo := Multiplicative (ZMod 2)
abbrev H (O : Type*) := CTwo × O
abbrev G (V O : Type*) := Multiplicative V × H O

def fiberPoint {V O : Type*} [AddCommGroup V] [Group O]
    (b : H O) (v : V) : G V O :=
  (Multiplicative.ofAdd v, b)

def normalizedAffineProfile {V O : Type*} [AddCommGroup V] [Group O]
    (A : H O → (V ≃+ V)) (c : H O → V)
    (f : Equiv.Perm (G V O)) : Prop :=
  A 1 = AddEquiv.refl V ∧ c 1 = 0 ∧
    ∀ v : V, ∀ h : H O,
      f (fiberPoint h v) = fiberPoint h (A h v + c h)

def normalizedRelativeDerivative {V O : Type*} [AddCommGroup V] [Group O]
    (f : Equiv.Perm (G V O)) (a : H O) (u : V) : Equiv.Perm (G V O) :=
  MathlibPlus.Open.ResearchFormalization.R1022.relativeDerivative f
    (fiberPoint a u)

def affineLinearPart {V O : Type*} [AddCommGroup V] [Group O]
    (A : H O → (V ≃+ V)) (a b : H O) (v : V) : V :=
  (A b).symm (A (b * a) v)

def affineTranslationPart {V O : Type*} [AddCommGroup V] [Group O]
    (A : H O → (V ≃+ V)) (c : H O → V)
    (a : H O) (u : V) (b : H O) : V :=
  (A b).symm
    (A (b * a) u + A a u + c (b * a) + c a + c b)

def affineFiberFormula {V O : Type*} [AddCommGroup V] [Group O]
    (A : H O → (V ≃+ V)) (c : H O → V)
    (a : H O) (u : V) (b : H O) (v : V) : V :=
  affineLinearPart A a b v + affineTranslationPart A c a u b

/-- The actual normalized group relative derivative has the displayed affine
fibre map for every normalized affine profile. -/
def relativeDerivativeFormula_claim39240 : Prop :=
  ∀ {V O : Type*} [Fintype V] [AddCommGroup V]
    [Fintype O] [Group O],
    (∀ v : V, v + v = 0) →
    Odd (Fintype.card O) →
    ∀ (A : H O → (V ≃+ V)) (c : H O → V)
      (f : Equiv.Perm (G V O)),
      normalizedAffineProfile A c f →
      ∀ (a b : H O) (u v : V),
        normalizedRelativeDerivative f a u (fiberPoint b v) =
          fiberPoint b (affineFiberFormula A c a u b v)

end MathlibPlus.Open.ResearchFormalization.R1565.Claim39240
