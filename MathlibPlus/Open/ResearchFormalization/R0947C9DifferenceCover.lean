import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0947C9DifferenceCover

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable section

abbrev C9 := ZMod 9

/-- The eight nonidentity residues of the additive cyclic group `C₉`. -/
def nonzeroC9 : Finset C9 :=
  (Finset.univ : Finset C9).erase 0

/-- Identity-inactive normalized active supports. -/
def normalizedActiveSupport (B : Finset C9) : Prop :=
  B ⊆ nonzeroC9

/-- The inactive fibres, including the identity fibre. -/
def inactiveFiberSet (B : Finset C9) : Finset C9 :=
  Finset.univ \ B

/-- The additive realization of `CC⁻¹` for an inactive fibre set `C`. -/
def differenceSet (C : Finset C9) : Finset C9 :=
  C.biUnion (fun c => C.image (fun d => c - d))

/-- Difference coverage of every active base point by two inactive base
points. -/
def differenceCovered (B : Finset C9) : Prop :=
  normalizedActiveSupport B ∧ B ⊆ differenceSet (inactiveFiberSet B)

/-- The complete normalized active-support carrier. -/
def activeSupportsC9 : Finset (Finset C9) :=
  nonzeroC9.powerset

/-- The supports satisfying the inactive-difference-cover criterion. -/
def coveredSupportsC9 : Finset (Finset C9) :=
  activeSupportsC9.filter differenceCovered

/-- The supports not satisfying the inactive-difference-cover criterion. -/
def residualSupportsC9 : Finset (Finset C9) :=
  activeSupportsC9.filter (fun B => ¬ differenceCovered B)

/-- The number of members of a support family having a specified active
support size. -/
def supportSizeCount (S : Finset (Finset C9)) (k : Nat) : Nat :=
  (S.filter (fun B => B.card = k)).card

/-- The complete `C₉` support census, including every displayed size row. -/
def c9SupportCountReceipt : Prop :=
  activeSupportsC9.card = 256 ∧
    coveredSupportsC9.card = 207 ∧
    residualSupportsC9.card = 49 ∧
    supportSizeCount activeSupportsC9 0 = 1 ∧
    supportSizeCount coveredSupportsC9 0 = 1 ∧
    supportSizeCount residualSupportsC9 0 = 0 ∧
    supportSizeCount activeSupportsC9 1 = 8 ∧
    supportSizeCount coveredSupportsC9 1 = 8 ∧
    supportSizeCount residualSupportsC9 1 = 0 ∧
    supportSizeCount activeSupportsC9 2 = 28 ∧
    supportSizeCount coveredSupportsC9 2 = 28 ∧
    supportSizeCount residualSupportsC9 2 = 0 ∧
    supportSizeCount activeSupportsC9 3 = 56 ∧
    supportSizeCount coveredSupportsC9 3 = 56 ∧
    supportSizeCount residualSupportsC9 3 = 0 ∧
    supportSizeCount activeSupportsC9 4 = 70 ∧
    supportSizeCount coveredSupportsC9 4 = 70 ∧
    supportSizeCount residualSupportsC9 4 = 0 ∧
    supportSizeCount activeSupportsC9 5 = 56 ∧
    supportSizeCount coveredSupportsC9 5 = 44 ∧
    supportSizeCount residualSupportsC9 5 = 12 ∧
    supportSizeCount activeSupportsC9 6 = 28 ∧
    supportSizeCount coveredSupportsC9 6 = 0 ∧
    supportSizeCount residualSupportsC9 6 = 28 ∧
    supportSizeCount activeSupportsC9 7 = 8 ∧
    supportSizeCount coveredSupportsC9 7 = 0 ∧
    supportSizeCount residualSupportsC9 7 = 8 ∧
    supportSizeCount activeSupportsC9 8 = 1 ∧
    supportSizeCount coveredSupportsC9 8 = 0 ∧
    supportSizeCount residualSupportsC9 8 = 1

/-- Claim 27469: the complete normalized identity-inactive `C₉` support
classification. -/
def completeNormalizedC9SupportClassification_claim27469 : Prop :=
  c9SupportCountReceipt

/-- The orbit of a support under all additive automorphisms of `C₉`. -/
def c9AutOrbit (B : Finset C9) : Finset (Finset C9) :=
  (Finset.univ : Finset (C9 ≃+ C9)).image (fun e => B.image (fun x => e x))

def c9Representative1 : Finset C9 :=
  {1, 2, 3, 4, 5}

def c9Representative2 : Finset C9 :=
  {1, 2, 3, 6, 7}

def c9Representative3 : Finset C9 :=
  {1, 2, 3, 4, 5, 6}

def c9Representative4 : Finset C9 :=
  {1, 2, 3, 4, 5, 7}

def c9Representative5 : Finset C9 :=
  {1, 2, 3, 4, 5, 8}

def c9Representative6 : Finset C9 :=
  {1, 2, 3, 4, 6, 7}

def c9Representative7 : Finset C9 :=
  {1, 2, 3, 6, 7, 8}

def c9Representative8 : Finset C9 :=
  {1, 2, 4, 5, 7, 8}

def c9Representative9 : Finset C9 :=
  {1, 2, 3, 4, 5, 6, 7}

def c9Representative10 : Finset C9 :=
  {1, 2, 3, 4, 5, 7, 8}

def c9Representative11 : Finset C9 :=
  {1, 2, 3, 4, 5, 6, 7, 8}

def c9RepresentativeVector : Fin 11 → Finset C9 :=
  ![c9Representative1, c9Representative2, c9Representative3,
    c9Representative4, c9Representative5, c9Representative6,
    c9Representative7, c9Representative8, c9Representative9,
    c9Representative10, c9Representative11]

/-- The residual support carrier as the union of the eleven listed
automorphism orbits. -/
def c9OrbitDecomposition : Prop :=
  residualSupportsC9 =
    c9AutOrbit c9Representative1 ∪ c9AutOrbit c9Representative2 ∪
      c9AutOrbit c9Representative3 ∪ c9AutOrbit c9Representative4 ∪
      c9AutOrbit c9Representative5 ∪ c9AutOrbit c9Representative6 ∪
      c9AutOrbit c9Representative7 ∪ c9AutOrbit c9Representative8 ∪
      c9AutOrbit c9Representative9 ∪ c9AutOrbit c9Representative10 ∪
      c9AutOrbit c9Representative11

/-- The displayed sizes of the eleven residual automorphism orbits. -/
def c9OrbitSizeReceipt : Prop :=
  (c9AutOrbit c9Representative1).card = 6 ∧
    (c9AutOrbit c9Representative2).card = 6 ∧
    (c9AutOrbit c9Representative3).card = 6 ∧
    (c9AutOrbit c9Representative4).card = 6 ∧
    (c9AutOrbit c9Representative5).card = 6 ∧
    (c9AutOrbit c9Representative6).card = 6 ∧
    (c9AutOrbit c9Representative7).card = 3 ∧
    (c9AutOrbit c9Representative8).card = 1 ∧
    (c9AutOrbit c9Representative9).card = 6 ∧
    (c9AutOrbit c9Representative10).card = 2 ∧
    (c9AutOrbit c9Representative11).card = 1

/-- The eleven listed supports are residual and their orbits are pairwise
disjoint. -/
def c9ResidualRepresentatives : Prop :=
  (∀ i : Fin 11, c9RepresentativeVector i ∈ residualSupportsC9) ∧
    (∀ i j : Fin 11, i ≠ j →
      Disjoint (c9AutOrbit (c9RepresentativeVector i))
        (c9AutOrbit (c9RepresentativeVector j)))

/-- Claim 27470: the forty-nine residual supports are exactly the eleven
listed `Aut(C₉)` orbits, with their displayed sizes. -/
def exactC9ResidualAutOrbits_claim27470 : Prop :=
  c9OrbitDecomposition ∧ c9OrbitSizeReceipt ∧ c9ResidualRepresentatives

/-- The fibre-preserving map specified by a family of permutations. -/
def c9FiberMapEquiv {K : Type*}
    (φ : C9 → Equiv.Perm K) : (K × C9) ≃ (K × C9) :=
  Equiv.prodCongrLeft φ

/-- The active base support of a fibre-preserving map. -/
def c9ActiveFiberSupport {K : Type*}
    (φ : C9 → Equiv.Perm K) : Set C9 :=
  {h | φ h ≠ Equiv.refl K}

/-- A profile with identity fibre inactive and active support exactly `B`. -/
def c9NormalizedProfile {K : Type*}
    (B : Finset C9) (φ : C9 → Equiv.Perm K) : Prop :=
  φ 0 = Equiv.refl K ∧ c9ActiveFiberSupport φ = (B : Set C9)

/-- The normalized relative derivative on the additive product carrier.
The order `s + x` is the finite-group derivative order. -/
def c9NormalizedRelativeDerivative {K : Type*} [AddGroup K]
    (φ : C9 → Equiv.Perm K) (x s : K × C9) : K × C9 :=
  (c9FiberMapEquiv φ).symm
    (c9FiberMapEquiv φ (s + x) - c9FiberMapEquiv φ x)

/-- One step in the orbit generated by all normalized relative derivatives. -/
def c9DerivativeStepRelation {K : Type*} [AddGroup K]
    (φ : C9 → Equiv.Perm K) (x y : K × C9) : Prop :=
  ∃ s : K × C9, y = c9NormalizedRelativeDerivative φ x s

/-- The orbit generated by the complete normalized relative-derivative
relation. -/
def c9DerivativeOrbit {K : Type*} [AddGroup K]
    (φ : C9 → Equiv.Perm K) (x : K × C9) : Set (K × C9) :=
  {y | Relation.EqvGen (c9DerivativeStepRelation φ) x y}

/-- Invariance under every normalized relative derivative. -/
def c9DerivativeInvariantSet {K : Type*} [AddGroup K]
    (φ : C9 → Equiv.Perm K) (S : Set (K × C9)) : Prop :=
  ∀ x s : K × C9,
    x ∈ S ↔ c9NormalizedRelativeDerivative φ x s ∈ S

/-- Setwise fixation of every generated relative-derivative orbit. -/
def c9DerivativeOrbitsFixed {K : Type*} [AddGroup K]
    (φ : C9 → Equiv.Perm K) : Prop :=
  ∀ x : K × C9,
    Set.image (c9FiberMapEquiv φ) (c9DerivativeOrbit φ x) =
      c9DerivativeOrbit φ x

/-- The explicit orbit-and-invariant-set harmlessness carrier used for both
CI and DCI. -/
def c9HarmlessProperty {K : Type*} [AddGroup K]
    (φ : C9 → Equiv.Perm K) : Prop :=
  c9DerivativeOrbitsFixed φ ∧
    (∀ S : Set (K × C9), c9DerivativeInvariantSet φ S →
      Set.image (c9FiberMapEquiv φ) S = S)

/-- The CI harmlessness consequence of the relative-derivative criterion. -/
def c9CIHarmless {K : Type*} [AddGroup K]
    (φ : C9 → Equiv.Perm K) : Prop :=
  c9HarmlessProperty φ

/-- The DCI harmlessness consequence of the relative-derivative criterion. -/
def c9DCIHarmless {K : Type*} [AddGroup K]
    (φ : C9 → Equiv.Perm K) : Prop :=
  c9HarmlessProperty φ

/-- A support is harmless when every finite additive fibre group and every
normalized profile on it has the two stated orbit-fixing consequences. -/
def c9ProfileHarmless (B : Finset C9) : Prop :=
  ∀ (K : Type) [Fintype K] [AddGroup K]
    (φ : C9 → Equiv.Perm K),
    c9NormalizedProfile B φ →
      c9CIHarmless φ ∧ c9DCIHarmless φ

/-- The support-size threshold, including the harmlessness consequence. -/
def c9ThresholdReceipt : Prop :=
  (∀ B : Finset C9, normalizedActiveSupport B → B.card ≤ 4 →
    differenceCovered B ∧ c9ProfileHarmless B) ∧
    supportSizeCount activeSupportsC9 5 = 56 ∧
    supportSizeCount coveredSupportsC9 5 = 44 ∧
    supportSizeCount residualSupportsC9 5 = 12 ∧
    (∀ B : Finset C9, normalizedActiveSupport B → B.card = 5 →
      differenceCovered B → c9ProfileHarmless B) ∧
    (∀ B : Finset C9, normalizedActiveSupport B → B.card = 6 →
      ¬ differenceCovered B) ∧
    (∀ B : Finset C9, normalizedActiveSupport B → B.card = 7 →
      ¬ differenceCovered B) ∧
    (∀ B : Finset C9, normalizedActiveSupport B → B.card = 8 →
      ¬ differenceCovered B)

/-- Claim 27471: supports through size four are difference-covered and CI/DCI
harmless, the forty-four covered size-five supports are harmless, exactly
twelve size-five supports survive, and sizes six through eight are uncovered. -/
def c9SupportSizeThreshold_claim27471 : Prop :=
  c9ThresholdReceipt

end

end MathlibPlus.Open.ResearchFormalization.R0947C9DifferenceCover
