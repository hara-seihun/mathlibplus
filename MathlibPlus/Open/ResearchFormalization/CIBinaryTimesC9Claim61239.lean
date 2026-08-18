import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9Claim61239

abbrev BinaryVector3 := Fin 3 → ZMod 2
abbrev BinaryTimesC9 := BinaryVector3 × ZMod 9

/-- The two-point connection set `{0_V} × {±1}` in `F₂^3 × C₉`. -/
def sourceConnectionSet : Set BinaryTimesC9 :=
  ({0} : Set BinaryVector3) ×ˢ
    ({(1 : ZMod 9), -(1 : ZMod 9)} : Set (ZMod 9))

/-- The two-point connection set `{0_V} × {±2}` in `F₂^3 × C₉`. -/
def targetConnectionSet : Set BinaryTimesC9 :=
  ({0} : Set BinaryVector3) ×ˢ
    ({(2 : ZMod 9), -(2 : ZMod 9)} : Set (ZMod 9))

/-- The standard `C₉` fibre above a binary vector. -/
def standardC9Fiber (x : BinaryVector3) : Set BinaryTimesC9 :=
  {p | p.1 = x}

/-- The binary quotient projection of `F₂^3 × C₉`. -/
def binaryQuotient (p : BinaryTimesC9) : BinaryVector3 :=
  p.1

/-- The identity product map on `V × C₉`. -/
def binaryTimesC9Identity (p : BinaryTimesC9) : BinaryTimesC9 :=
  (p.1, p.2)

/-- Pointed ordinary simple-undirected Cayley-graph isomorphism. -/
def pointedOrdinaryCayleyGraphIsomorphism
    (S T : Set BinaryTimesC9)
    (e : BinaryTimesC9 ≃ BinaryTimesC9) : Prop :=
  e 0 = 0 ∧
    ∀ x y : BinaryTimesC9,
      (SimpleGraph.addCayley S).Adj x y ↔
        (SimpleGraph.addCayley T).Adj (e x) (e y)

/-- The ordinary-CI-harmless group-automorphism conclusion. -/
def groupAutomorphismTransport
    (S T : Set BinaryTimesC9) : Prop :=
  ∃ α : BinaryTimesC9 ≃+ BinaryTimesC9,
    Set.image (fun p => α p) S = T

/-- The identity-multiplier equality asserted in the refuted stronger claim. -/
def identityMultiplierTransport
    (S T : Set BinaryTimesC9) : Prop :=
  T = Set.image binaryTimesC9Identity S

/-- The displayed multiplier-two map on the cyclic factor. -/
def multiplierTwoMap (p : BinaryTimesC9) : BinaryTimesC9 :=
  (p.1, (2 : ZMod 9) * p.2)

/-- Claim 61239: at rank three, the multiplier-two automorphism gives a
pointed fibre-preserving ordinary Cayley-graph isomorphism from the displayed
`{±1}` connection set to the displayed `{±2}` connection set, while the
identity multiplier does not transport them. -/
def claim61239 : Prop :=
  sourceConnectionSet ⊆
      (Set.univ : Set BinaryTimesC9) \ ({0} : Set BinaryTimesC9) ∧
    targetConnectionSet ⊆
      (Set.univ : Set BinaryTimesC9) \ ({0} : Set BinaryTimesC9) ∧
      (∀ s : BinaryTimesC9, s ∈ sourceConnectionSet → -s ∈ sourceConnectionSet) ∧
      (∀ t : BinaryTimesC9, t ∈ targetConnectionSet → -t ∈ targetConnectionSet) ∧
      ∃ f : BinaryTimesC9 ≃+ BinaryTimesC9,
        (∀ x : BinaryVector3, ∀ z : ZMod 9,
          f (x, z) = (x, (2 : ZMod 9) * z)) ∧
          f 0 = 0 ∧
          pointedOrdinaryCayleyGraphIsomorphism
            sourceConnectionSet targetConnectionSet f.toEquiv ∧
          (∀ x : BinaryVector3,
            Set.image (fun p => f p) (standardC9Fiber x) =
              standardC9Fiber x) ∧
          (∀ p : BinaryTimesC9,
            binaryQuotient (f p) = binaryQuotient p) ∧
          Set.image (fun p => f p) sourceConnectionSet = targetConnectionSet ∧
          targetConnectionSet ≠ sourceConnectionSet ∧
          ¬ identityMultiplierTransport sourceConnectionSet targetConnectionSet ∧
          groupAutomorphismTransport sourceConnectionSet targetConnectionSet

end MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9Claim61239
