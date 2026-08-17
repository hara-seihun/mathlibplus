import MathlibPlus.Open.ResearchFormalization.R1022

namespace MathlibPlus.Open.ResearchFormalization.R1565.Claim39242

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

def parityShearMap {V O : Type*} [AddCommGroup V] [Group O]
    (c₀ : V) : G V O → G V O :=
  fun x =>
    fiberPoint x.2
      (Multiplicative.toAdd x.1 + parityTranslate c₀ x.2)

def normalizedDerivativeInvariant {V O : Type*} [AddCommGroup V] [Group O]
    (f : Equiv.Perm (G V O)) (S : Set (G V O)) : Prop :=
  ∀ d : normalizedRelativeDerivativeGroup f, d.1 '' S = S

def cayleyRelation {K : Type*} [Group K]
    (S : Set K) (x y : K) : Prop := x⁻¹ * y ∈ S

def inverseClosed {K : Type*} [Group K] (S : Set K) : Prop :=
  ∀ x, x ∈ S ↔ x⁻¹ ∈ S

def directedCayleyTransport {V O : Type*} [AddCommGroup V] [Group O]
    (α : G V O ≃* G V O) (S T : Set (G V O)) : Prop :=
  ∀ x y,
    cayleyRelation S x y ↔ cayleyRelation T (α x) (α y)

def undirectedCayleyTransport {V O : Type*} [AddCommGroup V] [Group O]
    (α : G V O ≃* G V O) (S T : Set (G V O)) : Prop :=
  inverseClosed S ∧ inverseClosed T ∧ directedCayleyTransport α S T

/-- The period reduction gives the exact fibre identity, a parity-shear group
automorphism, and directed and inverse-closed Cayley transports. -/
def automorphismShadowForDerivativeInvariantSets_claim39242 : Prop :=
  ∀ {V O : Type*} [Fintype V] [AddCommGroup V]
    [Fintype O] [Group O],
    (∀ v : V, v + v = 0) →
    Odd (Fintype.card O) →
    ∀ (A : H O → (V ≃+ V)) (c : H O → V)
      (f : Equiv.Perm (G V O)),
      normalizedAffineProfile A c f →
      (∀ (b : H O) (v₀ : V),
        let X := fiberOrbitSection f b v₀
        Set.image (fun v : V => A b v + c b) X =
          Set.image (fun v : V => v + parityTranslate (c (zElement (O := O))) b) X) ∧
      ∃ α : G V O ≃* G V O,
        (∀ (v : V) (h : H O),
          α (fiberPoint h v) = parityShearMap (c (zElement (O := O)))
            (fiberPoint h v)) ∧
        (∀ x : G V O,
          Set.image (fun y => α y) (normalizedRelativeDerivativeOrbit f x) =
            Set.image f (normalizedRelativeDerivativeOrbit f x)) ∧
        (∀ S : Set (G V O), normalizedDerivativeInvariant f S →
          Set.image (fun y => α y) S = Set.image f S) ∧
        (∀ S : Set (G V O), normalizedDerivativeInvariant f S →
          directedCayleyTransport α S (Set.image f S) ∧
            (inverseClosed S →
              undirectedCayleyTransport α S (Set.image f S)))

end MathlibPlus.Open.ResearchFormalization.R1565.Claim39242
