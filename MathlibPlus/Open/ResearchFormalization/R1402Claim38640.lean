import MathlibPlus.Open.PrimeFiber

namespace MathlibPlus.Open.ResearchFormalization.R1402Claim38640

open Classical
open scoped BigOperators
open MathlibPlus.Open.PrimeFiber

noncomputable section

abbrev Scalar38640 := ZMod 3
abbrev Base38640 := Fin 5 → Scalar38640
abbrev Omega38640 := Scalar38640 × Base38640
abbrev LinearBase38640 := Base38640 ≃ₗ[Scalar38640] Base38640
abbrev LinearShift38640 := Base38640 →ₗ[Scalar38640] Scalar38640
abbrev MarkedPairCarrier38640 :=
  Equiv.Perm Base38640 × (Base38640 → Scalar38640)

def isMarkedPair38640 (pair : MarkedPairCarrier38640) : Prop :=
  pair.1 0 = 0 ∧ pair.2 0 = 0

/-- The normalized triangular transporter on the concrete central-line chart. -/
def fibreMap38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) : Equiv.Perm Omega38640 :=
  (Equiv.prodCongrLeft (fun b => Equiv.addRight (s b))).trans
    (Equiv.prodCongr (Equiv.refl Scalar38640) g)

def translationMap38640 (v : Omega38640) : Equiv.Perm Omega38640 :=
  Equiv.prodCongr (Equiv.addRight v.1) (Equiv.addRight v.2)

def sourceRegularCopy38640 : Subgroup (Equiv.Perm Omega38640) :=
  Subgroup.closure (Set.range translationMap38640)

def conjugateCopy38640 (f : Equiv.Perm Omega38640)
    (R : Subgroup (Equiv.Perm Omega38640)) :
    Subgroup (Equiv.Perm Omega38640) :=
  Subgroup.map (MulAut.conj f.symm).toMonoidHom R

/-- The target copy is literally the conjugate `R^{F_s}` in this chart. -/
def targetRegularCopy38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) : Subgroup (Equiv.Perm Omega38640) :=
  conjugateCopy38640 (fibreMap38640 s g) sourceRegularCopy38640

def generatedPair38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) : Subgroup (Equiv.Perm Omega38640) :=
  Subgroup.closure
    ((sourceRegularCopy38640 : Set (Equiv.Perm Omega38640)) ∪
      (targetRegularCopy38640 s g : Set (Equiv.Perm Omega38640)))

def origin38640 : Omega38640 := (0, 0)

def centralLinePointwise38640 (α : Equiv.Perm Omega38640) : Prop :=
  ∀ z : Scalar38640, α (z, 0) = (z, 0)

/-- Origin-fixing corrections in the normalizer interface. -/
def originFixingNormalizer38640 (α : Equiv.Perm Omega38640) : Prop :=
  conjugateCopy38640 α sourceRegularCopy38640 = sourceRegularCopy38640 ∧
    α origin38640 = origin38640 ∧
    centralLinePointwise38640 α

def normalizerCorrectionMap38640 (A : LinearBase38640)
    (ell : LinearShift38640) : Equiv.Perm Omega38640 :=
  (Equiv.prodCongrLeft (fun b => Equiv.addRight (ell b))).trans
    (Equiv.prodCongr (Equiv.refl Scalar38640) A.toEquiv)

def correctionAction38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (A : LinearBase38640)
    (ell : LinearShift38640) : Equiv.Perm Omega38640 :=
  (normalizerCorrectionMap38640 A ell).trans (fibreMap38640 s g)

def pointStabilizerSet38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) : Set (Equiv.Perm Omega38640) :=
  {k | k ∈ generatedPair38640 s g ∧ k origin38640 = origin38640}

def pointStabilizerSuborbit38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (x : Omega38640) : Set Omega38640 :=
  {y | ∃ k : Equiv.Perm Omega38640,
    k ∈ pointStabilizerSet38640 s g ∧ k x = y}

def fixesPointStabilizerSuborbits38640
    (s : Base38640 → Scalar38640) (g : Equiv.Perm Base38640)
    (q : Equiv.Perm Omega38640) : Prop :=
  ∀ x : Omega38640,
    Set.image q (pointStabilizerSuborbit38640 s g x) =
      pointStabilizerSuborbit38640 s g x

def projectedPointStabilizerComponent38640
    (s : Base38640 → Scalar38640) (g : Equiv.Perm Base38640)
    (O : Set Base38640) : Prop :=
  ∃ x : Omega38640,
    Set.image (fun y : Omega38640 => y.2)
      (pointStabilizerSuborbit38640 s g x) = O

/-- The normalized relative derivative on the quotient base. -/
def derivativeBase38640 (g : Equiv.Perm Base38640)
    (k : Base38640) : Equiv.Perm Base38640 :=
  ((Equiv.addRight k).trans g).trans
    ((Equiv.addRight (-(g k))).trans g.symm)

def derivativeVoltage38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (k h : Base38640) : Scalar38640 :=
  s (h + k) - s k - s (derivativeBase38640 g k h)

def derivativeBaseFamily38640 (g : Equiv.Perm Base38640) :
    Base38640 → Equiv.Perm Base38640 :=
  derivativeBase38640 g

def derivativeVoltageFamily38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) : Base38640 → Base38640 → Scalar38640 :=
  derivativeVoltage38640 s g

def componentData38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (O : Set Base38640)
    (b₀ : Base38640) (W : AddSubgroup Scalar38640)
    (t : Base38640 → Scalar38640) : Prop :=
  projectedPointStabilizerComponent38640 s g O ∧
    validPrimeFiberChoice
      (derivativeBaseFamily38640 g)
      (derivativeVoltageFamily38640 s g) O b₀ W t

def quietComponent38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (O : Set Base38640)
    (b₀ : Base38640) (W : AddSubgroup Scalar38640)
    (t : Base38640 → Scalar38640) : Prop :=
  componentData38640 s g O b₀ W t ∧ W = ⊥

def saturatedComponent38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (O : Set Base38640)
    (b₀ : Base38640) (W : AddSubgroup Scalar38640)
    (t : Base38640 → Scalar38640) : Prop :=
  componentData38640 s g O b₀ W t ∧ W = ⊤

def quietPointSet38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) : Set Base38640 :=
  {b | ∃ (O : Set Base38640) (b₀ : Base38640)
      (W : AddSubgroup Scalar38640) (t : Base38640 → Scalar38640),
      quietComponent38640 s g O b₀ W t ∧ b ∈ O}

def projectedComponentsPreserved38640
    (s : Base38640 → Scalar38640) (g : Equiv.Perm Base38640)
    (A : LinearBase38640) : Prop :=
  ∀ O : Set Base38640,
    projectedPointStabilizerComponent38640 s g O →
      Set.image (fun b : Base38640 => g (A b)) O = O

def componentEquation38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (A : LinearBase38640)
    (ell : LinearShift38640) : Prop :=
  projectedComponentsPreserved38640 s g A ∧
    ∀ (O : Set Base38640) (b₀ : Base38640)
      (W : AddSubgroup Scalar38640) (t : Base38640 → Scalar38640),
      quietComponent38640 s g O b₀ W t →
      ∀ b : Base38640, b ∈ O →
        ell b = t (g (A b)) - t b - s (A b)

/-- The equation-defined affine repair fibre for a fixed linear base shadow. -/
def equationRepairSet38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (A : LinearBase38640) :
    Set LinearShift38640 :=
  {ell | componentEquation38640 s g A ell}

/-- The actual marked-pair/point-stabilizer repair fibre. -/
def closureRepairSet38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (A : LinearBase38640) :
    Set LinearShift38640 :=
  {ell | fixesPointStabilizerSuborbits38640 s g
      (correctionAction38640 s g A ell)}

def quietRightSide38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (A : LinearBase38640)
    (d : Base38640 → Scalar38640) : Prop :=
  ∀ (O : Set Base38640) (b₀ : Base38640)
    (W : AddSubgroup Scalar38640) (t : Base38640 → Scalar38640),
    quietComponent38640 s g O b₀ W t →
    ∀ b : Base38640, b ∈ O →
      d b = t (g (A b)) - t b - s (A b)

def quietCoefficientEvaluation38640
    (Q : Set Base38640) : (Q →₀ Scalar38640) →ₗ[Scalar38640] Base38640 :=
  Finsupp.linearCombination Scalar38640 (fun b : Q => (b : Base38640))

def quietRelation38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (c : (quietPointSet38640 s g →₀ Scalar38640)) : Prop :=
  quietCoefficientEvaluation38640 (quietPointSet38640 s g) c = 0

def quietDefect38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (A : LinearBase38640)
    (d : Base38640 → Scalar38640)
    (c : (quietPointSet38640 s g →₀ Scalar38640)) : Scalar38640 :=
  c.sum (fun b a => a * d b)

def relationDefectFree38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (A : LinearBase38640) : Prop :=
  projectedComponentsPreserved38640 s g A ∧
    ∃ d : Base38640 → Scalar38640,
      quietRightSide38640 s g A d ∧
        ∀ c : (quietPointSet38640 s g →₀ Scalar38640),
          quietRelation38640 s g c → quietDefect38640 s g A d c = 0

def relationSeparator38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (A : LinearBase38640) : Prop :=
  ∃ d : Base38640 → Scalar38640,
    quietRightSide38640 s g A d ∧
      ∃ c : (quietPointSet38640 s g →₀ Scalar38640),
        quietRelation38640 s g c ∧ quietDefect38640 s g A d c ≠ 0

def affineSolutionDimension38640
    (s : Base38640 → Scalar38640) (g : Equiv.Perm Base38640) : ℕ :=
  5 - Module.finrank Scalar38640
    (Submodule.span Scalar38640
      (quietPointSet38640 s g : Set Base38640))

def repairCard38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) (A : LinearBase38640) : ℕ :=
  Nat.card {ell : LinearShift38640 //
    ell ∈ closureRepairSet38640 s g A}

def completeResidual38640 (s : Base38640 → Scalar38640)
    (g : Equiv.Perm Base38640) : Set LinearShift38640 :=
  ⋃ A : LinearBase38640, closureRepairSet38640 s g A

/-- The complete normalizer-shift interface, including the actual marked pair,
point-stabilizer suborbits, quiet/saturated voltage components, relation
separators, affine fibres, and the full residual union. -/
def claim38640 : Prop :=
  ∀ (pair : MarkedPairCarrier38640),
    isMarkedPair38640 pair →
      let g := pair.1
      let s := pair.2
      (∀ α : Equiv.Perm Omega38640,
        originFixingNormalizer38640 α →
          ∃! Aell : LinearBase38640 × LinearShift38640,
            ∀ z : Scalar38640, ∀ b : Base38640,
              α (z, b) = (z + Aell.2 b, Aell.1 b)) ∧
      (∀ (A : LinearBase38640) (ell : LinearShift38640)
        (z : Scalar38640) (b : Base38640),
        correctionAction38640 s g A ell (z, b) =
          (z + ell b + s (A b), g (A b))) ∧
      (∀ O : Set Base38640,
        projectedPointStabilizerComponent38640 s g O →
          ∃ (b₀ : Base38640) (W : AddSubgroup Scalar38640)
            (t : Base38640 → Scalar38640),
            componentData38640 s g O b₀ W t ∧
              (W = ⊥ ∨ W = ⊤)) ∧
      (∀ (A : LinearBase38640),
        closureRepairSet38640 s g A =
          equationRepairSet38640 s g A) ∧
      (∀ (A : LinearBase38640),
        closureRepairSet38640 s g A = ∅ ↔
          (¬ projectedComponentsPreserved38640 s g A ∨
            relationSeparator38640 s g A)) ∧
      (∀ (A : LinearBase38640),
        closureRepairSet38640 s g A ≠ ∅ →
          repairCard38640 s g A =
            3 ^ affineSolutionDimension38640 s g) ∧
      (∀ (A : LinearBase38640),
        equationRepairSet38640 s g A = ∅ ∨
          ∃ ell₀ : LinearShift38640,
            equationRepairSet38640 s g A =
              {ell | ∀ b : Base38640,
                b ∈ quietPointSet38640 s g → ell b = ell₀ b}) ∧
      completeResidual38640 s g =
        {ell | ∃ A : LinearBase38640, ell ∈ closureRepairSet38640 s g A}

end

end MathlibPlus.Open.ResearchFormalization.R1402Claim38640

namespace MathlibPlus.Open.ResearchFormalization.R1402Claim38642

open Classical
open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R1402Claim38640

noncomputable section

abbrev Scalar38642 := Scalar38640
abbrev Base38642 := Base38640
abbrev LinearBase38642 := LinearBase38640
abbrev LinearShift38642 := LinearShift38640
abbrev MarkedPairCarrier38642 := MarkedPairCarrier38640

def quietPointSet38642 (pair : MarkedPairCarrier38642)
    (A : LinearBase38642) : Set Base38642 :=
  {b | b ∈ quietPointSet38640 pair.2 pair.1 ∧
    projectedComponentsPreserved38640 pair.2 pair.1 A}

def quietEvaluationMap38642 (pair : MarkedPairCarrier38642)
    (A : LinearBase38642) :
    (quietPointSet38642 pair A →₀ Scalar38642) →ₗ[Scalar38642] Base38642 :=
  quietCoefficientEvaluation38640 (quietPointSet38642 pair A)

def quietRelation38642 (pair : MarkedPairCarrier38642)
    (A : LinearBase38642)
    (c : (quietPointSet38642 pair A →₀ Scalar38642)) : Prop :=
  quietEvaluationMap38642 pair A c = 0

def quietDefect38642 (pair : MarkedPairCarrier38642)
    (A : LinearBase38642) (d : Base38642 → Scalar38642)
    (c : (quietPointSet38642 pair A →₀ Scalar38642)) : Scalar38642 :=
  c.sum (fun b a => a * d b)

def extendsQuietRightSide38642 (pair : MarkedPairCarrier38642)
    (A : LinearBase38642) (d : Base38642 → Scalar38642) : Prop :=
  ∃ ell : LinearShift38642,
    ∀ b : quietPointSet38642 pair A, ell b = d b

def extensionCard38642 (pair : MarkedPairCarrier38642)
    (A : LinearBase38642) (d : Base38642 → Scalar38642) : ℕ :=
  Nat.card {ell : LinearShift38642 //
    ∀ b : quietPointSet38642 pair A, ell b = d b}

def affineExtensionDimension38642 (pair : MarkedPairCarrier38642)
    (A : LinearBase38642) : ℕ :=
  5 - Module.finrank Scalar38642
    (Submodule.span Scalar38642
      (quietPointSet38642 pair A : Set Base38642))

def basisEvaluation38642 (pair : MarkedPairCarrier38642)
    (A : LinearBase38642) : Prop :=
  ∀ b : quietPointSet38642 pair A,
    quietEvaluationMap38642 pair A (Finsupp.single b 1) = (b : Base38642)

def relationDefectFree38642 (pair : MarkedPairCarrier38642)
    (A : LinearBase38642) : Prop :=
  projectedComponentsPreserved38640 pair.2 pair.1 A ∧
    ∃ d : Base38642 → Scalar38642,
      quietRightSide38640 pair.2 pair.1 A d ∧
        ∀ c : (quietPointSet38642 pair A →₀ Scalar38642),
          quietRelation38642 pair A c → quietDefect38642 pair A d c = 0

def separator38642 (pair : MarkedPairCarrier38642)
    (A : LinearBase38642) : Prop :=
  ∃ d : Base38642 → Scalar38642,
    quietRightSide38640 pair.2 pair.1 A d ∧
      ∃ c : (quietPointSet38642 pair A →₀ Scalar38642),
        quietRelation38642 pair A c ∧ quietDefect38642 pair A d c ≠ 0

/-- The dual quiet-span and relation-annihilation statement on the actual
marked R-1402 pair, including the point-stabilizer repair family. -/
def claim38642 : Prop :=
  ∀ (pair : MarkedPairCarrier38642),
    isMarkedPair38640 pair →
      (∀ (A : LinearBase38642),
        projectedComponentsPreserved38640 pair.2 pair.1 A →
          ∀ d : Base38642 → Scalar38642,
            quietRightSide38640 pair.2 pair.1 A d →
              basisEvaluation38642 pair A ∧
              ((extendsQuietRightSide38642 pair A d) ↔
                ∀ c : (quietPointSet38642 pair A →₀ Scalar38642),
                  quietRelation38642 pair A c →
                    quietDefect38642 pair A d c = 0) ∧
              (extendsQuietRightSide38642 pair A d →
                extensionCard38642 pair A d =
                  3 ^ affineExtensionDimension38642 pair A) ∧
              (∀ c : (quietPointSet38642 pair A →₀ Scalar38642),
                quietRelation38642 pair A c →
                  quietDefect38642 pair A d c ≠ 0 →
                    ¬ extendsQuietRightSide38642 pair A d)) ∧
      ((∃ A : LinearBase38642,
          closureRepairSet38640 pair.2 pair.1 A ≠ ∅) ↔
        ∃ A : LinearBase38642,
          relationDefectFree38642 pair A)

end

end MathlibPlus.Open.ResearchFormalization.R1402Claim38642
