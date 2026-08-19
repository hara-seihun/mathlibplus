import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9UnipotentTransferClaim61331

abbrev ElementaryNinePlane := ZMod 3 × ZMod 3
abbrev CyclicNineProduct (V : Type*) := V × ZMod 9
abbrev UnipotentProduct (V : Type*) := V × ElementaryNinePlane

/-- A finite additive group of exponent two is the group carrier used for the
binary factor. -/
def elementaryAbelianTwo (V : Type*) [AddCommGroup V] [Fintype V] : Prop :=
  ∀ x : V, x + x = 0

/-- Inverse-closure for an additive connection set. -/
def inverseClosed {A : Type*} [AddGroup A] (S : Set A) : Prop :=
  ∀ x : A, x ∈ S ↔ -x ∈ S

/-- The identity-free condition for an additive connection set. -/
def identityFree {A : Type*} [Zero A] (S : Set A) : Prop :=
  (0 : A) ∉ S

/-- The five inverse atoms of the cyclic group of order nine, in the order
used by the displayed atom transport. -/
def cyclicNineAtom (i : Fin 5) : Set (ZMod 9) :=
  if i.val = 0 then
    ({0} : Set (ZMod 9))
  else if i.val = 1 then
    ({(3 : ZMod 9), -(3 : ZMod 9)} : Set (ZMod 9))
  else if i.val = 2 then
    ({(1 : ZMod 9), -(1 : ZMod 9)} : Set (ZMod 9))
  else if i.val = 3 then
    ({(4 : ZMod 9), -(4 : ZMod 9)} : Set (ZMod 9))
  else
    ({(2 : ZMod 9), -(2 : ZMod 9)} : Set (ZMod 9))

/-- The corresponding five inverse atoms of `F₃²`. -/
def elementaryNineAtom (i : Fin 5) : Set ElementaryNinePlane :=
  if i.val = 0 then
    ({((0 : ZMod 3), (0 : ZMod 3))} : Set ElementaryNinePlane)
  else if i.val = 1 then
    ({((1 : ZMod 3), (0 : ZMod 3)),
      -((1 : ZMod 3), (0 : ZMod 3))} : Set ElementaryNinePlane)
  else if i.val = 2 then
    ({((0 : ZMod 3), (1 : ZMod 3)),
      -((0 : ZMod 3), (1 : ZMod 3))} : Set ElementaryNinePlane)
  else if i.val = 3 then
    ({((1 : ZMod 3), (1 : ZMod 3)),
      -((1 : ZMod 3), (1 : ZMod 3))} : Set ElementaryNinePlane)
  else
    ({((2 : ZMod 3), (1 : ZMod 3)),
      -((2 : ZMod 3), (1 : ZMod 3))} : Set ElementaryNinePlane)

/-- The atomwise extension of the displayed bijection from cyclic atoms to
ternary-plane atoms. -/
def theta (D : Set (ZMod 9)) : Set ElementaryNinePlane :=
  {e | ∃ i : Fin 5, cyclicNineAtom i ⊆ D ∧ e ∈ elementaryNineAtom i}

/-- The cyclic section of a connection set over a binary basepoint. -/
def cyclicSection {V : Type*}
    (S : Set (CyclicNineProduct V)) (v : V) : Set (ZMod 9) :=
  {z | (v, z) ∈ S}

/-- Sectionwise transport of a connection set through `theta`. -/
def thetaLift {V : Type*}
    (S : Set (CyclicNineProduct V)) : Set (UnipotentProduct V) :=
  {q | q.2 ∈ theta (cyclicSection S q.1)}

/-- The displayed unipotent shear `J(a,b)=(a+b,b)`. -/
def unipotentShear : ElementaryNinePlane → ElementaryNinePlane :=
  fun q => (q.1 + q.2, q.2)

/-- The fixed line of the displayed unipotent shear. -/
def unipotentFixedLine : Set ElementaryNinePlane :=
  {q | q.2 = 0}

/-- The power of `J` indexed by the canonical representative of a class in
`Z/3Z`. -/
def unipotentPower (p : ZMod 3) : ElementaryNinePlane → ElementaryNinePlane :=
  unipotentShear^[p.val]

/-- The exponent `p(u)` in `u ∈ {±4^p}` for a unit modulo nine. -/
def cyclicUnitExponent (u : (ZMod 9)ˣ) : ZMod 3 :=
  if (u : ZMod 9) = (4 : ZMod 9) ∨
      (u : ZMod 9) = (5 : ZMod 9) then
    1
  else if (u : ZMod 9) = (2 : ZMod 9) ∨
      (u : ZMod 9) = (7 : ZMod 9) then
    2
  else
    0

/-- A pointed ordinary Cayley-graph isomorphism on an additive carrier. -/
def pointedCayleyGraphIsomorphism
    {A : Type*} [AddGroup A]
    (S T : Set A) (f : A → A) : Prop :=
  Function.Bijective f ∧
    f 0 = 0 ∧
      ∀ x y : A,
        (x ≠ y ∧ y - x ∈ S) ↔
          (f x ≠ f y ∧ f y - f x ∈ T)

/-- The affine cyclic-fibre form with an arbitrary base permutation, a unit at
 each basepoint, and an arbitrary cyclic carry. -/
def affineCyclicFibreMap
    {V : Type*}
    (β : V ≃ V) (u : V → (ZMod 9)ˣ) (c : V → ZMod 9) :
    CyclicNineProduct V → CyclicNineProduct V :=
  fun q => (β q.1, (u q.1 : ZMod 9) * q.2 + c q.1)

/-- The pointed permutation prescribed by the inverse-atom transfer. -/
def unipotentFibreMap
    {V : Type*}
    (β : V ≃ V) (u : V → (ZMod 9)ˣ) :
    UnipotentProduct V → UnipotentProduct V :=
  fun q => (β q.1, unipotentPower (cyclicUnitExponent (u q.1)) q.2)

/-- The restricted unipotent group-automorphism shadow. -/
def unipotentShadow
    {V : Type*} [AddCommGroup V] (M : V ≃+ V) (p : ZMod 3) :
    UnipotentProduct V → UnipotentProduct V :=
  fun q => (M q.1, unipotentPower p q.2)

/-- The corresponding restricted cyclic group-automorphism shadow. -/
def cyclicShadow
    {V : Type*} [AddCommGroup V] (M : V ≃+ V) (p : ZMod 3) :
    CyclicNineProduct V → CyclicNineProduct V :=
  fun q => (M q.1, (4 : ZMod 9) ^ p.val * q.2)

/-- The versions of the two shadows with an overall inversion on the cyclic
factor. -/
def signedUnipotentShadow
    {V : Type*} [AddCommGroup V] (M : V ≃+ V) (p : ZMod 3) :
    UnipotentProduct V → UnipotentProduct V :=
  fun q => (M q.1, -(unipotentPower p q.2))

def signedCyclicShadow
    {V : Type*} [AddCommGroup V] (M : V ≃+ V) (p : ZMod 3) :
    CyclicNineProduct V → CyclicNineProduct V :=
  fun q => (M q.1, -((4 : ZMod 9) ^ p.val * q.2))

/-- Claim 61331: every pointed affine standard-`C₉`-fibre presentation
transfers atom-for-atom to the displayed unipotent `F₃²` chart, and the
restricted additive-automorphism shadows agree in both charts. -/
def claim61331 : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Fintype V],
    elementaryAbelianTwo V →
      ∀ (S T : Set (CyclicNineProduct V)),
        identityFree S →
        identityFree T →
        inverseClosed S →
        inverseClosed T →
          ∀ (f : CyclicNineProduct V → CyclicNineProduct V)
            (β : V ≃ V) (u : V → (ZMod 9)ˣ) (c : V → ZMod 9),
            pointedCayleyGraphIsomorphism S T f →
            f = affineCyclicFibreMap β u c →
              pointedCayleyGraphIsomorphism
                  (thetaLift S) (thetaLift T) (unipotentFibreMap β u) ∧
                (∀ (M : V ≃+ V) (p : ZMod 3),
                  (Set.image (unipotentShadow M p) (thetaLift S) = thetaLift T ↔
                    Set.image (cyclicShadow M p) S = T)) ∧
                (∀ (M : V ≃+ V) (p : ZMod 3),
                  (Set.image (signedUnipotentShadow M p) (thetaLift S) = thetaLift T ↔
                    Set.image (signedCyclicShadow M p) S = T))

end MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9UnipotentTransferClaim61331
