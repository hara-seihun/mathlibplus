import MathlibPlus.Open.ResearchFormalization.R1022

namespace MathlibPlus.Open.ResearchFormalization.R1565.Claim39241

abbrev CTwo := Multiplicative (ZMod 2)
abbrev H (O : Type*) := CTwo × O
abbrev G (V O : Type*) := Multiplicative V × H O

def epsilon {O : Type*} (h : H O) : ZMod 2 :=
  Multiplicative.toAdd h.1

def zElement {O : Type*} [One O] : H O :=
  (Multiplicative.ofAdd (1 : ZMod 2), 1)

def parityTranslate {V O : Type*} [AddGroup V]
    (c₀ : V) (h : H O) : V :=
  if epsilon h = 0 then 0 else c₀

def fiberPoint {V O : Type*} [AddCommGroup V] [Group O]
    (b : H O) (v : V) : G V O :=
  (Multiplicative.ofAdd v, b)

def normalizedAffineProfile {V O : Type*} [AddCommGroup V] [Group O]
    (A : H O → (V ≃+ V)) (c : H O → V)
    (f : Equiv.Perm (G V O)) : Prop :=
  A 1 = AddEquiv.refl V ∧ c 1 = 0 ∧
    ∀ v : V, ∀ h : H O,
      f (fiberPoint h v) = fiberPoint h (A h v + c h)

def normalizedRelativeDerivativeGroup {V O : Type*} [AddCommGroup V] [Group O]
    (f : Equiv.Perm (G V O)) : Subgroup (Equiv.Perm (G V O)) :=
  Subgroup.closure
    (Set.range (MathlibPlus.Open.ResearchFormalization.R1022.relativeDerivative f))

def normalizedRelativeDerivativeOrbit {V O : Type*} [AddCommGroup V] [Group O]
    (f : Equiv.Perm (G V O)) (x : G V O) : Set (G V O) :=
  {y | ∃ d : normalizedRelativeDerivativeGroup f, d.1 x = y}

def fiberSection {V O : Type*} [AddCommGroup V] [Group O]
    (b : H O) (X : Set (G V O)) : Set V :=
  {v | fiberPoint b v ∈ X}

def fiberOrbitSection {V O : Type*} [AddCommGroup V] [Group O]
    (f : Equiv.Perm (G V O)) (b : H O) (v₀ : V) : Set V :=
  fiberSection b (normalizedRelativeDerivativeOrbit f (fiberPoint b v₀))

def translationPeriod {V : Type*} [AddGroup V]
    (X : Set V) : Set V :=
  {t | Set.image (fun v : V => v + t) X = X}

def affineLinearPart {V O : Type*} [AddCommGroup V] [Group O]
    (A : H O → (V ≃+ V)) (a b : H O) (v : V) : V :=
  (A b).symm (A (b * a) v)

def moduloPeriod {V : Type*} [AddGroup V]
    (P : Set V) (x y : V) : Prop := x - y ∈ P

def oddLayer {O : Type*} [One O] : Set (H O) :=
  {h | h.1 = (1 : CTwo)}

def evenLayer {O : Type*} [One O] : Set (H O) :=
  {h | h.1 = (zElement (O := O)).1}

def oddSquareClosure {O : Type*} [Group O] : Prop :=
  ∀ o : O,
    Subgroup.closure ({((1 : CTwo), o) ^ 2} : Set (H O)) =
      Subgroup.closure ({((1 : CTwo), o)} : Set (H O))

/-- Every normalized relative-derivative orbit in an arbitrary fibre has the
period and parity residuals stated by the quotient argument. -/
def periodQuotientParityResiduals_claim39241 : Prop :=
  ∀ {V O : Type*} [Fintype V] [AddCommGroup V]
    [Fintype O] [Group O],
    (∀ v : V, v + v = 0) →
    Odd (Fintype.card O) →
    ∀ (A : H O → (V ≃+ V)) (c : H O → V)
      (f : Equiv.Perm (G V O)),
      normalizedAffineProfile A c f →
      ∀ (b : H O) (v₀ : V),
        let X := fiberOrbitSection f b v₀
        let P := translationPeriod X
        (∀ a : H O,
          Set.image (fun t : V => affineLinearPart A a b t) P = P) ∧
        (∀ a : H O, ∀ v : V,
          A (b * a) v + A a v ∈ P) ∧
        (∀ a : H O, ∀ v : V,
          moduloPeriod P (A (b * a) v) (A a v)) ∧
        (∀ a : H O,
          moduloPeriod P (c (b ^ 2 * a)) (c a)) ∧
        (∀ v : V,
          moduloPeriod P (A b v) v) ∧
        oddSquareClosure (O := O) ∧
        (b ∈ oddLayer (O := O) →
          c b ∈ P) ∧
        (b ∈ evenLayer (O := O) →
          moduloPeriod P (c b) (c (zElement (O := O)))) ∧
        (∀ v : V, A b v - v ∈ P) ∧
        c b + parityTranslate (c (zElement (O := O))) b ∈ P

end MathlibPlus.Open.ResearchFormalization.R1565.Claim39241
