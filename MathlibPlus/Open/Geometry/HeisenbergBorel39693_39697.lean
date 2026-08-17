import Mathlib

namespace MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

open Classical

noncomputable section

abbrev F7 := ZMod 7
abbrev W7 := F7 × F7
abbrev Perm7 := Equiv.Perm W7

/-- The upper-triangular linear maps on the actual two-dimensional `F₇` plane. -/
def upperTriangularLinearSet7 : Set Perm7 :=
  {f | ∃ a b d : F7, a ≠ 0 ∧ d ≠ 0 ∧
    ∀ z : W7, f z = (a * z.1 + b * z.2, d * z.2)}

def linearBorel7 : Subgroup Perm7 :=
  Subgroup.closure upperTriangularLinearSet7

/-- The affine Borel group acting on `W=F₇²`. -/
def affineBorelSet7 : Set Perm7 :=
  {f | ∃ t : W7, ∃ b : linearBorel7,
    ∀ z : W7, f z = t + (b : Perm7) z}

def affineBorel7 : Subgroup Perm7 :=
  Subgroup.closure affineBorelSet7

def translationSet7 : Set Perm7 :=
  {f | ∃ t : W7, ∀ z : W7, f z = t + z}

def translate7 (t : W7) : Perm7 :=
  Equiv.addRight t

def translationGroup7 : Subgroup Perm7 :=
  Subgroup.closure translationSet7

def shearSet7 : Set Perm7 :=
  {f | ∃ c : F7, ∀ z : W7, f z = (z.1 + c * z.2, z.2)}

def shearGroup7 : Subgroup Perm7 :=
  Subgroup.closure shearSet7

def heisenbergGroup7 : Subgroup Perm7 :=
  Subgroup.closure (translationSet7 ∪ shearSet7)

def flagTranslationSet7 : Set Perm7 :=
  {f | ∃ a : F7, ∀ z : W7, f z = (a, 0) + z}

def flagTranslationGroup7 : Subgroup Perm7 :=
  Subgroup.closure flagTranslationSet7

def flagVectors7 : Set W7 :=
  {t | t.2 = 0}

def horizontalLine7 (y : F7) : Set W7 :=
  {z | z.2 = y}

def orbit7 (K : Subgroup Perm7) (x : W7) : Set W7 :=
  {y | ∃ g : K, (g : Perm7) x = y}

def transitive7 (K : Subgroup Perm7) : Prop :=
  ∀ x y : W7, ∃ g : K, (g : Perm7) x = y

def translationCore7 (K : Subgroup Perm7) : Set W7 :=
  {t | translate7 t ∈ K}

def translationStabilizer7 (K : Subgroup Perm7) : Set W7 :=
  {t | ∀ x y : W7,
    y ∈ orbit7 K x ↔ translate7 t y ∈ orbit7 K x}

def strictlyContains7 (S T : Set W7) : Prop :=
  S ⊆ T ∧ ¬ T ⊆ S

def is7Subgroup7 (H : Subgroup Perm7) : Prop :=
  ∃ n : ℕ, Nat.card H = 7 ^ n

def normalIn7 (H K : Subgroup Perm7) : Prop :=
  H ≤ K ∧ ∀ k : K, ∀ h : H,
    (k : Perm7) * (h : Perm7) * (k : Perm7)⁻¹ ∈ H

def normalSylow7 (P Γ : Subgroup Perm7) : Prop :=
  P ≤ Γ ∧ normalIn7 P Γ ∧ is7Subgroup7 P ∧
    ∀ Q : Subgroup Perm7, Q ≤ Γ → is7Subgroup7 Q → Q ≤ P

def heisenbergCore7 (Γ : Subgroup Perm7) : Subgroup Perm7 :=
  Γ ⊓ heisenbergGroup7

def generatedBy7 (g : Perm7) : Subgroup Perm7 :=
  Subgroup.closure ({g} : Set Perm7)

/-- The cyclic normal-form permutation used in the two cyclic cases. -/
def cyclicGeneratorFormula7 (c a b : F7) (g : Perm7) : Prop :=
  ∀ z : W7, g z = (z.1 + c * z.2 + a, z.2 + b)

def fixedPointSet7 (g : Perm7) : Set W7 :=
  {z | g z = z}

def affineLineAction7 (Γ : Subgroup Perm7) (y : F7) : Prop :=
  ∃ scale shift : Γ → F7,
    (∀ h : Γ, scale h ≠ 0) ∧
      ∀ h : Γ, ∀ x : F7,
        (h : Perm7) (x, y) = (scale h * x + shift h, y)

def qInvariant7 (c a b : F7) (z : W7) : F7 :=
  z.1 - (c * (2 * b)⁻¹) * z.2 ^ 2 -
    (a * b⁻¹ - c * (2 : F7)⁻¹) * z.2

def qFiber7 (c a b u : F7) : Set W7 :=
  {z | qInvariant7 c a b z = u}

def affineQAction7 (Γ : Subgroup Perm7) (c a b : F7) : Prop :=
  ∃ scale shift : Γ → F7,
    (∀ h : Γ, scale h ≠ 0) ∧
      ∀ h : Γ, ∀ z : W7,
        qInvariant7 c a b ((h : Perm7) z) =
          scale h * qInvariant7 c a b z + shift h

def cyclicCoreHypothesis7 (Γ : Subgroup Perm7) (g : Perm7) : Prop :=
  let P := generatedBy7 g
  P ≤ Γ ∧ P ≤ heisenbergGroup7 ∧ P = heisenbergCore7 Γ ∧
    normalSylow7 P Γ ∧
      Nat.Coprime (Nat.card Γ / Nat.card P) 7

/-- Claim 39693: the `b=0` cyclic shear has a horizontal fixed line, the
prime-to-seven affine action fixes a point on it, and the common translation
stabilizer is trivial. -/
def claim39693_b_zero_cyclic_case : Prop :=
  ∀ (Γ : Subgroup Perm7) (c a : F7) (g : Perm7),
    Γ ≤ affineBorel7 →
    c ≠ 0 → cyclicGeneratorFormula7 c a 0 g →
    cyclicCoreHypothesis7 Γ g →
    fixedPointSet7 g = horizontalLine7 ((-a) * c⁻¹) ∧
      affineLineAction7 Γ ((-a) * c⁻¹) ∧
      (∃ z : W7,
        z ∈ horizontalLine7 ((-a) * c⁻¹) ∧
        orbit7 Γ z = ({z} : Set W7)) ∧
      translationStabilizer7 Γ = ({(0 : W7)} : Set W7)

/-- Claim 39694: the `b≠0` cyclic orbits are the fibers of the displayed
quadratic invariant, and the affine quotient action fixes one such fiber. -/
def claim39694_quadratic_orbit_invariant : Prop :=
  ∀ (Γ : Subgroup Perm7) (c a b : F7) (g : Perm7),
    Γ ≤ affineBorel7 →
    c ≠ 0 → b ≠ 0 → cyclicGeneratorFormula7 c a b g →
    cyclicCoreHypothesis7 Γ g →
    (∀ z : W7,
      orbit7 (generatedBy7 g) z = qFiber7 c a b (qInvariant7 c a b z)) ∧
      affineQAction7 Γ c a b ∧
      (∃ u : F7, ∀ h : Γ, ∀ z : W7,
        qInvariant7 c a b z = u →
          qInvariant7 c a b ((h : Perm7) z) = u)

/-- Claim 39696: after restricting to a core with nonzero shear projection,
the three actual affine-Heisenberg orbit/stabilizer cases are exhaustive. -/
def claim39696_heisenberg_core_stabilizer_trichotomy : Prop :=
  ∀ (Γ : Subgroup Perm7), Γ ≤ affineBorel7 →
    let P := heisenbergCore7 Γ
    ¬ (P ≤ translationGroup7) →
      (transitive7 P ∧
          translationStabilizer7 P = (Set.univ : Set W7) ∧
          translationStabilizer7 Γ = (Set.univ : Set W7)) ∨
        (¬ transitive7 P ∧ flagTranslationGroup7 ≤ P ∧
          (∀ x : W7, orbit7 P x = horizontalLine7 x.2) ∧
          translationStabilizer7 P = flagVectors7 ∧
          translationStabilizer7 Γ = flagVectors7) ∨
        ((∃ g : Perm7, P = generatedBy7 g) ∧ Nat.card P = 7 ∧
          P ⊓ flagTranslationGroup7 = ⊥ ∧
          translationStabilizer7 P = ({(0 : W7)} : Set W7) ∧
          translationStabilizer7 Γ = ({(0 : W7)} : Set W7))

/-- Claim 39697: the only excess common translation stabilizer is the
transitive order-49 core with flag-line translation core; the full order-343
Heisenberg group has no excess because its translation core is already W. -/
def claim39697_exact_excess_stabilizer_classification : Prop :=
  (∀ (P : Subgroup Perm7), P ≤ heisenbergGroup7 →
    (strictlyContains7 (translationCore7 P) (translationStabilizer7 P) ↔
      Nat.card P = 49 ∧ transitive7 P ∧
        translationCore7 P = flagVectors7)) ∧
    Nat.card heisenbergGroup7 = 343 ∧
      transitive7 heisenbergGroup7 ∧
        translationCore7 heisenbergGroup7 = (Set.univ : Set W7) ∧
          translationStabilizer7 heisenbergGroup7 = (Set.univ : Set W7)

end
end MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697
