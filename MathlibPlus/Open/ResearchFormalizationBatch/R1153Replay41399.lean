import MathlibPlus.Open.ResearchFormalizationBatch.GroupTheory

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch.R1153Replay41399

open MathlibPlus.Open.ResearchFormalizationBatch

abbrev K2 := ZMod 2
abbrev H2 := BooleanQuotient (ZMod 3)
abbrev TwistedCarrier := H2 × K2

/-- The normalized nonsplit quaternion extension over `C₃ × C₂²`. -/
def quaternionCocycle (h u : H2) : K2 :=
  h.2.1 * u.2.1 + h.2.2 * u.2.2 + h.2.2 * u.2.1

def twistedMul (x y : TwistedCarrier) : TwistedCarrier :=
  (x.1 + y.1, x.2 + y.2 + quaternionCocycle x.1 y.1)

def twistedInv (x : TwistedCarrier) : TwistedCarrier :=
  (-x.1, -x.2 - quaternionCocycle x.1 (-x.1))

/-- The normalized Boolean switching and its character-shear comparison. -/
def liftSwitch (b : H2 → K2) : TwistedCarrier → TwistedCarrier :=
  fun x => (x.1, x.2 + b x.1)

def characterShear (χ : H2 →+ K2) : TwistedCarrier → TwistedCarrier :=
  fun x => (x.1, x.2 + χ x.1)

def twistedAutomorphism (f : TwistedCarrier → TwistedCarrier) : Prop :=
  Function.Bijective f ∧
    ∀ x y, f (twistedMul x y) = twistedMul (f x) (f y)

/-- The relative derivative relation uses every base direction. -/
def derivativeStep (b : H2 → K2) (u : H2) (x : TwistedCarrier) : TwistedCarrier :=
  (x.1, x.2 + b (x.1 + u) + b x.1 + b u)

def derivativeOrbit (b : H2 → K2) (x : TwistedCarrier) : Set TwistedCarrier :=
  {y | Relation.ReflTransGen
      (fun s t => ∃ u : H2, t = derivativeStep b u s) x y}

def orbitShadow (b : H2 → K2) (χ : H2 →+ K2) : Prop :=
  ∀ x : TwistedCarrier,
    Set.image (liftSwitch b) (derivativeOrbit b x) =
      Set.image (characterShear χ) (derivativeOrbit b x)

def twistedCayleyRelation (S : Set TwistedCarrier)
    (x y : TwistedCarrier) : Prop :=
  ∃ s, s ∈ S ∧ y = twistedMul x s

def carriesTwistedCayley (f : TwistedCarrier → TwistedCarrier)
    (S T : Set TwistedCarrier) : Prop :=
  ∀ x y,
    twistedCayleyRelation S x y ↔
      twistedCayleyRelation T (f x) (f y)

def twistedInverseClosed (S : Set TwistedCarrier) : Prop :=
  ∀ x, x ∈ S → twistedInv x ∈ S

def characterShearWitness (b : H2 → K2) (χ : H2 →+ K2) : Prop :=
  (∀ h, h ∈ linearitySet31633 b → χ h = b h) ∧
    twistedAutomorphism (characterShear χ) ∧
      orbitShadow b χ ∧
        (∀ S T : Set TwistedCarrier,
          carriesTwistedCayley (liftSwitch b) S T →
            carriesTwistedCayley (characterShear χ) S T) ∧
          (∀ S T : Set TwistedCarrier,
            twistedInverseClosed S →
              twistedInverseClosed T →
                carriesTwistedCayley (liftSwitch b) S T →
                  carriesTwistedCayley (characterShear χ) S T)

def normalizedSwitchingSet : Set (H2 → K2) :=
  {b | b 0 = 0}

def characterShearWitnessCount (b : H2 → K2) : ℕ :=
  Set.ncard {χ : H2 →+ K2 | characterShearWitness b χ}

/-- Claim 41399: the complete normalized `C₃ × Q₈` Boolean-switching census. -/
def claim41399 : Prop :=
  Set.ncard normalizedSwitchingSet = 2 ^ 11 ∧
    (∀ b : H2 → K2, b 0 = 0 → 0 < characterShearWitnessCount b) ∧
      Set.ncard {b : H2 → K2 |
        b 0 = 0 ∧ characterShearWitnessCount b = 0} = 0 ∧
      Set.ncard {b : H2 → K2 |
        b 0 = 0 ∧ characterShearWitnessCount b = 4} = 1888 ∧
      Set.ncard {b : H2 → K2 |
        b 0 = 0 ∧ characterShearWitnessCount b = 2} = 144 ∧
      Set.ncard {b : H2 → K2 |
        b 0 = 0 ∧ characterShearWitnessCount b = 1} = 16

end MathlibPlus.Open.ResearchFormalizationBatch.R1153Replay41399
