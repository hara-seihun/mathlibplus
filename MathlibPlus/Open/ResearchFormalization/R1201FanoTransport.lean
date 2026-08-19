import MathlibPlus.Open.ResearchFormalization.R1144DistinctLabels

namespace MathlibPlus.Open.ResearchFormalization.R1201

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1144DistinctLabels

abbrev C7 := ZMod 7
abbrev PointPair := C7 × C7

def affineSetImage (d : (C7)ˣ) (t : C7) (S : Set C7) : Set C7 :=
  {y | ∃ x ∈ S, y = (d : C7) * x + t}

def affineSystemImage (d : (C7)ˣ) (t : C7)
    (F : Set (Set C7)) : Set (Set C7) :=
  Set.image (affineSetImage d t) F

def fanoSystemKind (F : Set (Set C7)) : Prop :=
  F = fanoA ∨ F = fanoB

def cyclicFanoSystem (F : Set (Set C7)) : Set (Set C7) :=
  fanoSupportSystemCarrier F

def cyclicFanoShape (S : Set C7) : Prop :=
  (∃ t : C7, S = ({t} : Set C7)) ∨
    (∃ t : C7, S = ({t} : Set C7)ᶜ) ∨
      ∃ F : Set (Set C7),
        fanoSystemKind F ∧ S ∈ cyclicFanoSystem F

def sourceFiber (T : Set C7) (m n x : C7) : Set PointPair :=
  {z | z.1 = x ∧ z.2 ∈ translateSet T (m * x + n)}

def targetFiber (T : Set C7) (m n x : C7) : Set PointPair :=
  {z | z.1 = x ∧ z.2 ∈ translateSet T (m * x + n)}

def baseTransport (d : (C7)ˣ) (t₀ : C7)
    (T T' : Set C7) : Prop :=
  affineSetImage d t₀ T = T'

def triangularMap (a : (C7)ˣ) (r₀ : C7) (d : (C7)ˣ)
    (m n m' n' t₀ : C7) : PointPair → PointPair :=
  fun z =>
    ((a : C7) * z.1 + r₀,
      (d : C7) * z.2 +
        (m' * (a : C7) - (d : C7) * m) * z.1 +
        t₀ + m' * r₀ + n' - (d : C7) * n)

def properFiberTransport
    (a : (C7)ˣ) (r₀ : C7) (d : (C7)ˣ)
    (m n m' n' t₀ : C7) (T T' : Set C7) : Prop :=
  ∀ x : C7,
    Set.image
        (triangularMap a r₀ d m n m' n' t₀)
        (sourceFiber T m n x) =
      targetFiber T' m' n' ((a : C7) * x + r₀)

def cyclicFanoSystemsAffinelyEquivalent : Prop :=
  ∀ F F' : Set (Set C7),
    fanoSystemKind F → fanoSystemKind F' →
      ∃ d : (C7)ˣ, ∃ t₀ : C7,
        affineSystemImage d t₀ (cyclicFanoSystem F) =
          cyclicFanoSystem F'

def triangularTransportStatement : Prop :=
  ∀ (a : (C7)ˣ) (r₀ : C7) (d : (C7)ˣ) (t₀ : C7)
    (m n m' n' : C7) (T T' : Set C7),
    cyclicFanoShape T → cyclicFanoShape T' →
      baseTransport d t₀ T T' →
        properFiberTransport a r₀ d m n m' n' t₀ T T'

def claim41943_affineFanoEquivalence : Prop :=
  cyclicFanoSystemsAffinelyEquivalent ∧ triangularTransportStatement

def claim41944_explicitTriangularTransport : Prop :=
  triangularTransportStatement

end

end MathlibPlus.Open.ResearchFormalization.R1201
