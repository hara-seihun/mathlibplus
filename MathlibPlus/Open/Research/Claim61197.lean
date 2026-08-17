import MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Research.Claim61197

open MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160

abbrev F2 := MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.F2
abbrev F3 := MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.F3
abbrev A := MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.A
abbrev B := MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.B
abbrev G := MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.G
abbrev LinearAutomorphism :=
  MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.LinearAutomorphism
abbrev InverseAtom :=
  MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.InverseAtom
abbrev IncidenceComponent :=
  MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.IncidenceComponent

/-- The eight ternary control values other than the zero vector. -/
def nonzeroTernaryVectors : Finset B :=
  Finset.univ.erase 0

/-- A nonempty control subset of `B \ {0}`. -/
abbrev BinaryControl :=
  {K : Finset B // K ⊆ nonzeroTernaryVectors ∧ K.Nonempty}

/-- A nonzero binary linear functional. -/
abbrev BinaryFunctional :=
  {ell : A →ₗ[F2] F2 // ell ≠ 0}

/-- An unordered pair of distinct ternary values. -/
abbrev TernaryPair :=
  {P : Finset F3 // P.card = 2}

structure GateParameters where
  order : Bool
  binaryCoordinate : Fin 4
  binaryControl : BinaryControl
  ternaryCoordinate : Fin 2
  binaryFunctional : BinaryFunctional
  ternaryPair : TernaryPair

/-- The sum of the two entries of the selected unordered ternary pair. -/
def ternaryPairSum (P : TernaryPair) : F3 :=
  ∑ r ∈ P.1, r

/-- The transposition of the two selected ternary values. -/
def ternaryPairSwap (P : TernaryPair) (r : F3) : F3 :=
  if r ∈ P.1 then ternaryPairSum P - r else r

/-- The binary-fibre controlled coordinate toggle `u_{i,K}`. -/
def binaryControlledGate (i : Fin 4) (K : BinaryControl) : G → G :=
  fun x =>
    (x.1 + (if x.2 ∈ K.1 then Pi.single i 1 else 0), x.2)

/-- The ternary-fibre controlled coordinate transposition `v_{j,ell,{r,s}}`. -/
def ternaryControlledGate (j : Fin 2) (ell : BinaryFunctional)
    (P : TernaryPair) : G → G :=
  fun x =>
    (x.1,
      Function.update x.2 j
        (if ell.1 x.1 = 1 then ternaryPairSwap P (x.2 j) else x.2 j))

/-- Both stipulated orders of the two controlled gates. -/
def twoWayControlledComposition (p : GateParameters) : G → G :=
  if p.order then
    fun x =>
      ternaryControlledGate p.ternaryCoordinate p.binaryFunctional p.ternaryPair
        (binaryControlledGate p.binaryCoordinate p.binaryControl x)
  else
    fun x =>
      binaryControlledGate p.binaryCoordinate p.binaryControl
        (ternaryControlledGate p.ternaryCoordinate p.binaryFunctional p.ternaryPair x)

/-- Pointedness and involutivity of the two literal controlled gates. -/
def pointedInvolutions (p : GateParameters) : Prop :=
  Function.Involutive
      (binaryControlledGate p.binaryCoordinate p.binaryControl) ∧
    binaryControlledGate p.binaryCoordinate p.binaryControl 0 = 0 ∧
    Function.Involutive
      (ternaryControlledGate p.ternaryCoordinate p.binaryFunctional p.ternaryPair) ∧
    ternaryControlledGate p.ternaryCoordinate p.binaryFunctional p.ternaryPair 0 = 0

/-- One automorphism is chosen before taking any union of incidence components. -/
def commonGateComponentShadow (f : G ≃ G) : Prop :=
  ∃ alpha : LinearAutomorphism,
    (∀ C : IncidenceComponent f,
      alphaLabelImage alpha (sourceLabels C) = targetLabels C) ∧
    (∀ K : Set (IncidenceComponent f),
      ordinaryGraphIsomorphism f
        (sourceConnectionSet K) (targetConnectionSet K) ∧
      groupAutomorphismAction alpha '' sourceConnectionSet K =
        targetConnectionSet K)

/-- The exact identity-free inverse-closed ordinary-Cayley defect excluded through the
component shadow. -/
def commonGateDefect (f : G ≃ G) : Prop :=
  ∃ K : Set (IncidenceComponent f),
    let S := sourceConnectionSet K
    let T := targetConnectionSet K
    identityFree S ∧ inverseClosed S ∧
      identityFree T ∧ inverseClosed T ∧
      ordinaryGraphIsomorphism f S T ∧
      ¬ ∃ alpha : LinearAutomorphism,
        groupAutomorphismAction alpha '' S = T

/-- Claim 61197: all 183,600 one-binary-gate/one-ternary-gate compositions have
one simultaneous automorphism shadow for every inverse-atom component and every
component union, so neither order supplies the stated ordinary-Cayley defect. -/
def claim61197 : Prop :=
  Nat.card Bool * Nat.card (Fin 4) * Nat.card BinaryControl *
      Nat.card (Fin 2) * Nat.card BinaryFunctional *
      Nat.card TernaryPair = 2 * 4 * (2 ^ 8 - 1) * 2 * (2 ^ 4 - 1) * 3 ∧
    2 * 4 * (2 ^ 8 - 1) * 2 * (2 ^ 4 - 1) * 3 = 183600 ∧
    ∀ p : GateParameters,
      pointedInvolutions p ∧
        ∃ f : G ≃ G,
          (∀ x : G, f x = twoWayControlledComposition p x) ∧
            commonGateComponentShadow f ∧
              ¬ commonGateDefect f

end MathlibPlus.Open.Research.Claim61197
