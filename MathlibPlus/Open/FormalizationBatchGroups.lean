import Mathlib

namespace MathlibPlus.Open.FormalizationBatchGroups

noncomputable section

open scoped BigOperators

/-- Explicit normality and conjugacy predicates for finite groups. -/
def normalSubgroupPredicate {A : Type*} [Group A] (N : Subgroup A) : Prop :=
  ∀ a x : A, x ∈ N → a * x * a⁻¹ ∈ N

def finiteIntersectionOrder {A : Type*} [Fintype A] [Group A]
    (H N : Subgroup A) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : A => x ∈ H ∧ x ∈ N)).card

def conjugateSubgroups {A : Type*} [Group A]
    (H K : Subgroup A) : Prop :=
  ∃ a : A, ∀ x : A, x ∈ K ↔ a⁻¹ * x * a ∈ H

def conjugateIntersections {A : Type*} [Group A]
    (H K N : Subgroup A) : Prop :=
  ∃ a : A, ∀ x : A,
    (x ∈ K ∧ x ∈ N) ↔
      (a⁻¹ * x * a ∈ H ∧ a⁻¹ * x * a ∈ N)

/-- Conjugate subgroups have conjugate intersections with a normal subgroup and
therefore equal finite intersection orders. -/
def normalIntersectionConjugacyClaim26797 : Prop :=
  ∀ (A : Type*) [Fintype A] [Group A]
    (N H K : Subgroup A),
    normalSubgroupPredicate N →
    conjugateSubgroups H K →
    conjugateIntersections H K N ∧
      finiteIntersectionOrder H N = finiteIntersectionOrder K N

/-- Translates and periods in an additive group. -/
def addTranslate {M : Type*} [Add M] (u : M) (S : Set M) : Set M :=
  {x | ∃ s, s ∈ S ∧ x = u + s}

def periodSet {M : Type*} [Add M] (S : Set M) : Set M :=
  {p | addTranslate p S = S}

/-- The translation-design period lemma, including both coset-map forms and the
point-difference equivalence. -/
def translationDesignPeriodClaim51301 : Prop :=
  ∀ (M : Type*) [AddCommGroup M]
    (A B : Set M) (φ ψ : Equiv.Perm M),
    (∀ u : M, φ '' addTranslate u A = addTranslate (ψ u) B) →
    (∀ u : M,
      φ '' addTranslate u (periodSet A) =
        addTranslate (φ u) (periodSet B)) ∧
    (∀ u : M,
      ψ '' addTranslate u (periodSet A) =
        addTranslate (ψ u) (periodSet B)) ∧
    (∀ u v : M,
      u - v ∈ periodSet A ↔ ψ u - ψ v ∈ periodSet B)

abbrev S₃ := Equiv.Perm (Fin 3)
abbrev OppositeS₃Group (A : Type*) := A × S₃

def oppositeS₃F {A : Type*} [AddGroup A]
    (q : S₃ → Equiv.Perm A) : OppositeS₃Group A → OppositeS₃Group A
  | (v, h) => (q h v, h⁻¹)

def oppositeS₃FInv {A : Type*} [AddGroup A]
    (q : S₃ → Equiv.Perm A) : OppositeS₃Group A → OppositeS₃Group A
  | (v, h) => ((q (h⁻¹)).symm v, h⁻¹)

def oppositeS₃Mul {A : Type*} [AddGroup A]
    (x y : OppositeS₃Group A) : OppositeS₃Group A :=
  (x.1 + y.1, x.2 * y.2)

def oppositeS₃Inv {A : Type*} [AddGroup A]
    (x : OppositeS₃Group A) : OppositeS₃Group A :=
  (-x.1, x.2⁻¹)

def oppositeS₃D {A : Type*} [AddGroup A]
    (q : S₃ → Equiv.Perm A)
    (g x : OppositeS₃Group A) : OppositeS₃Group A :=
  oppositeS₃Mul (oppositeS₃F q (oppositeS₃Mul x g))
    (oppositeS₃Inv (oppositeS₃F q g))

def oppositeS₃U {A : Type*} [AddGroup A]
    (q : S₃ → Equiv.Perm A)
    (g x : OppositeS₃Group A) : OppositeS₃Group A :=
  oppositeS₃FInv q (oppositeS₃D q g x)

def oppositeS₃Theta (k h : S₃) : S₃ := k⁻¹ * h * k

/-- The explicit common-chart formula for the opposite-S₃ construction. -/
def oppositeS3CommonChartDerivativeClaim52239 : Prop :=
  ∀ (A : Type*) [Fintype A] [AddCommGroup A],
    Nat.Coprime (Fintype.card A) 6 →
    ∀ (q : S₃ → Equiv.Perm A), q 1 = Equiv.refl A →
    ∀ (u : A) (k : S₃) (v : A) (h : S₃),
      oppositeS₃U q (u, k) (v, h) =
        ( (q (oppositeS₃Theta k h)).symm
            (q (h * k) (v + u) - q k u),
          oppositeS₃Theta k h )

/-- A directed Cayley relation on an additive vector space. -/
def directedCayleyRelation {V : Type*} [Add V]
    (S : Set V) : Set (V × V) :=
  {p | ∃ x a, a ∈ S ∧ p = (x, x + a)}

def relationImage {V W : Type*}
    (f : V → W) (R : Set (V × V)) : Set (W × W) :=
  Set.image (fun p => (f p.1, f p.2)) R

/-- A finite pair of connection-set tuples and their directed Cayley relations in
an elementary-abelian rank-bounded carrier. -/
def directedCayleyRelationTupleClaim52219
    (p r t : ℕ) (hp : Nat.Prime p) (hr₁ : 1 ≤ r) (hr₃ : r ≤ 3)
    (A B : Fin t → Set (Fin r → ZMod p)) :
    (Fin t → Set ((Fin r → ZMod p) × (Fin r → ZMod p))) ×
      (Fin t → Set ((Fin r → ZMod p) × (Fin r → ZMod p))) :=
  ( (fun j => directedCayleyRelation (A j)),
    (fun j => directedCayleyRelation (B j)) )

/-- The all-prime rank-at-most-three tuple shadow theorem. -/
def pureRankAtMostThreeTupleShadowClaim52220 : Prop :=
  ∀ (p r : ℕ), Nat.Prime p → 1 ≤ r → r ≤ 3 →
    let V := Fin r → ZMod p
    ∀ (t : ℕ) (A B : Fin t → Set V) (f : V ≃ V),
      f 0 = 0 →
      (∀ j : Fin t, relationImage f (directedCayleyRelation (A j)) =
        directedCayleyRelation (B j)) →
      ∃ α : V ≃ₗ[ZMod p] V,
        ∀ j : Fin t, Set.image α (A j) = B j

/-- Square-free natural numbers. -/
def squareFreeNatural (m : ℕ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → ¬q ^ 2 ∣ m

def unitMultiple {m : ℕ} (u : (ZMod m)ˣ) (S : Set (ZMod m)) : Set (ZMod m) :=
  (fun x : ZMod m => (u : ZMod m) * x) '' S

/-- A single unit is the multiplier for every simultaneous cyclic relation. -/
def commonMultiplierCyclicRelationsClaim55346 : Prop :=
  ∀ (m : ℕ),
    1 < m → m % 2 = 1 → squareFreeNatural m →
    ∀ (t : ℕ) (S T : Fin t → Set (ZMod m))
      (f : Equiv.Perm (ZMod m)),
      f 0 = 0 →
      (∀ j : Fin t, ∀ x y : ZMod m,
        (y - x ∈ S j ↔ f y - f x ∈ T j)) →
      ∃ u : (ZMod m)ˣ, ∀ j : Fin t, unitMultiple u (S j) = T j

end

end MathlibPlus.Open.FormalizationBatchGroups
