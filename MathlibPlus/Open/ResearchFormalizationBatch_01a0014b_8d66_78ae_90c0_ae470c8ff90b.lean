import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a0014b_8d66_78ae_90c0_ae470c8ff90b

noncomputable section

namespace GeometricPolarization

abbrev Source := Fin 10
abbrev Target := Fin 3
abbrev Poly (ι : Type*) := MvPolynomial ι ℤ

def sourceVariable (i : Source) : Poly Source :=
  MvPolynomial.X i

def targetVariable (i : Target) : Poly Target :=
  MvPolynomial.X i

def geometricEvaluation (f : Poly Source) : Poly Target :=
  MvPolynomial.eval₂Hom (MvPolynomial.C)
    (fun i : Source => targetVariable ⟨0, by omega⟩ *
      targetVariable ⟨1, by omega⟩ ^ i.1) f

def firstPolarization (f : Poly Source) : Poly Target :=
  ∑ i : Source,
    if 1 ≤ i.1 then
      targetVariable ⟨2, by omega⟩ ^ i.1 *
        geometricEvaluation (MvPolynomial.pderiv i f)
    else 0

def f6 : Poly Source :=
  sourceVariable ⟨2, by omega⟩ ^ 2 -
    sourceVariable ⟨1, by omega⟩ * sourceVariable ⟨3, by omega⟩

def markedF6 : Poly Source :=
  sourceVariable ⟨9, by omega⟩ * f6

/-- The two exact cap identities, including sharpness of the forced square. -/
def sharpLegalCap : Prop :=
  firstPolarization f6 =
      -targetVariable ⟨0, by omega⟩ * targetVariable ⟨1, by omega⟩ *
        targetVariable ⟨2, by omega⟩ *
        (targetVariable ⟨2, by omega⟩ - targetVariable ⟨1, by omega⟩) ^ 2 ∧
    ¬ ((targetVariable ⟨2, by omega⟩ - targetVariable ⟨1, by omega⟩) ^ 3 ∣
      firstPolarization f6) ∧
    firstPolarization markedF6 =
      -targetVariable ⟨0, by omega⟩ ^ 2 * targetVariable ⟨1, by omega⟩ ^ 10 *
        targetVariable ⟨2, by omega⟩ *
        (targetVariable ⟨2, by omega⟩ - targetVariable ⟨1, by omega⟩) ^ 2 ∧
    ¬ ((targetVariable ⟨2, by omega⟩ - targetVariable ⟨1, by omega⟩) ^ 3 ∣
      firstPolarization markedF6)

end GeometricPolarization

namespace CommonCentralFibre

variable {p : ℕ} [Fact p.Prime]
variable {D B : Type*}
variable [AddCommGroup D] [AddCommGroup B]
variable [Module (ZMod p) D] [Module (ZMod p) B]
variable [FiniteDimensional (ZMod p) D] [FiniteDimensional (ZMod p) B]

def addRightPerm (G : Type*) [AddGroup G] (a : G) : Equiv.Perm G :=
  { toFun := fun x => x + a
    invFun := fun x => x - a
    left_inv := by intro x; simp [sub_eq_add_neg, add_assoc]
    right_inv := by intro x; simp [sub_eq_add_neg, add_assoc] }

def qPerm (g : Equiv.Perm B) (s : B → D) : Equiv.Perm (D × B) :=
  { toFun := fun x => (x.1 + s x.2, g x.2)
    invFun := fun x => (x.1 - s (g.symm x.2), g.symm x.2)
    left_inv := by
      rintro ⟨d, b⟩
      simp [sub_eq_add_neg, add_assoc]
    right_inv := by
      rintro ⟨d, b⟩
      simp [sub_eq_add_neg, add_assoc] }

def rightRegularSubgroup (G : Type*) [AddGroup G] : Subgroup (Equiv.Perm G) :=
  Subgroup.closure (Set.range (addRightPerm G))

def centralTranslationSet : Set (Equiv.Perm (D × B)) :=
  (Subgroup.closure (Set.range (fun d : D => addRightPerm (D × B) (d, 0))) : Set _)

def blockKernelSet (X : Subgroup (Equiv.Perm (D × B))) : Set (Equiv.Perm (D × B)) :=
  {u | u ∈ X ∧ ∀ d : D, ∀ b : B, (u (d, b)).2 = b}

def generatedCentralFibreGroup (g : Equiv.Perm B) (s : B → D) :
    Subgroup (Equiv.Perm (D × B)) :=
  Subgroup.closure
    ((rightRegularSubgroup (D × B) : Set (Equiv.Perm (D × B))) ∪
      {qPerm g s})

def relativeStep (g : Equiv.Perm B) (k h : B) : B :=
  g.symm (g (h + k) - g k)

def beta (g : Equiv.Perm B) (s : B → D) (k h : B) : D :=
  s (h + k) - s k - s (relativeStep g k h)

/-- Relative-derivative criterion for the literal common-central-fibre model. -/
def relativeDerivativeCriterion (g : Equiv.Perm B) (s : B → D) : Prop :=
  s 0 = 0 → g 0 = 0 →
    (blockKernelSet (generatedCentralFibreGroup g s) = centralTranslationSet ↔
      ∃ t : B → D, t 0 = 0 ∧
        ∀ k h : B, t (relativeStep g k h) - t h = beta g s k h)

/-- Equivalent all-pairs vector switching formulation. -/
def vectorSwitchingDecomposition (g : Equiv.Perm B) (s : B → D) : Prop :=
  s 0 = 0 → g 0 = 0 →
    (blockKernelSet (generatedCentralFibreGroup g s) = centralTranslationSet ↔
      ∃ a b : B → D,
        a 0 = 0 ∧ b 0 = 0 ∧
          ∀ x y : B,
            s x - s y = a (x - y) + b (g x - g y))

end CommonCentralFibre

end
end MathlibPlus.Open.ResearchFormalizationBatch_01a0014b_8d66_78ae_90c0_ae470c8ff90b
