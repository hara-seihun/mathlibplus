import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.CIElementaryAbelian3Rank7GaleShadowClaim61322

noncomputable section

abbrev F3 := ZMod 3
abbrev A := Fin 3 → F3
abbrev B := Fin 4 → F3
abbrev Covector := A →ₗ[F3] F3
abbrev V := B × A

def scalarComponent (F : B → A) (u : Covector) : B → F3 :=
  fun x => u (F x)

def quietDirections (F : B → A) (u : Covector) : Set B :=
  {d | ∀ x : B,
    scalarComponent F u (x + d) - scalarComponent F u x =
      scalarComponent F u d}

def displacementSubmodule (F : B → A) (b : B) : Submodule F3 A :=
  Submodule.span F3
    {z | ∃ x : B, z = F b + F x - F (x + b)}

def quietDependencyConditions (F : B → A) (m : ℕ)
    (u : Fin m → Covector) (d : Fin m → B) : Prop :=
  (∀ i : Fin m, u i ≠ 0) ∧
    (∀ i : Fin m, d i ≠ 0) ∧
    (∀ i : Fin m, d i ∈ quietDirections F (u i)) ∧
    (∑ i : Fin m,
        TensorProduct.tmul F3 (u i) (d i)) = 0

def quietDependencySlopeSum (F : B → A) (m : ℕ)
    (u : Fin m → Covector) (d : Fin m → B) : F3 :=
  ∑ i : Fin m, scalarComponent F (u i) (d i)

def quietDependencyTheorem : Prop :=
  ∀ (F : B → A), F 0 = 0 →
    ∀ m : ℕ, m ≤ 10 →
      ∀ (u : Fin m → Covector) (d : Fin m → B),
        quietDependencyConditions F m u d →
          quietDependencySlopeSum F m u d = 0

def projectiveClass (u : Covector) : Set Covector :=
  {v | ∃ c : F3, c ≠ 0 ∧ v = c • u}

def projectiveQuietClasses (F : B → A) : Set (Set Covector) :=
  {C | ∃ u : Covector, u ≠ 0 ∧ C = projectiveClass u ∧
    quietDirections F u ≠ ({0} : Set B)}

def atMostTenQuietProjectiveClasses (F : B → A) : Prop :=
  Set.ncard (projectiveQuietClasses F) ≤ 10

def qShear (F : B → A) : V → V :=
  fun z => (z.1, z.2 + F z.1)

def linearShear (ell : B →ₗ[F3] A) : V → V :=
  fun z => (z.1, z.2 + ell z.1)

def directedCayleyAdjacency (S : Set V) (x y : V) : Prop :=
  y - x ∈ S

def directedCayleyRelationIso (q : V → V) (S T : Set V) : Prop :=
  Function.Bijective q ∧
    ∀ x y : V,
      directedCayleyAdjacency S x y ↔
        directedCayleyAdjacency T (q x) (q y)

def identityFree (S : Set V) : Prop :=
  (0 : V) ∉ S

def inverseClosed (S : Set V) : Prop :=
  ∀ ⦃s : V⦄, s ∈ S → -s ∈ S

def undirectedCayleyAdjacency (S : Set V) (x y : V) : Prop :=
  x ≠ y ∧ y - x ∈ S

def ordinaryUndirectedCayleyCIDefect
    (S T : Set V) (q : V → V) : Prop :=
  identityFree S ∧
    identityFree T ∧
    inverseClosed S ∧
    inverseClosed T ∧
    Function.Bijective q ∧
    (∀ x y : V,
      undirectedCayleyAdjacency S x y ↔
        undirectedCayleyAdjacency T (q x) (q y)) ∧
    ¬ ∃ e : V ≃+ V, (fun z => e z) '' S = T

def verticalShearAddEquiv (ell : B →ₗ[F3] A) : Prop :=
  ∃ e : V ≃+ V, ∀ z : V, e z = linearShear ell z

def literalGroupLinearConnectionSetShadow
    (F : B → A) (ell : B →ₗ[F3] A) : Prop :=
  ∀ (S T : Set V),
    directedCayleyRelationIso (qShear F) S T →
      linearShear ell '' S = T

def noOrdinaryUndirectedCayleyCIDefect
    (F : B → A) : Prop :=
  ∀ (S T : Set V),
    identityFree S →
    identityFree T →
    inverseClosed S →
    inverseClosed T →
    directedCayleyRelationIso (qShear F) S T →
      ¬ ordinaryUndirectedCayleyCIDefect S T (qShear F)

def rankSevenQuietClassCorollary : Prop :=
  ∀ (F : B → A), F 0 = 0 →
    atMostTenQuietProjectiveClasses F →
      ∃ ell : B →ₗ[F3] A,
        (∀ b : B,
          F b - ell b ∈ displacementSubmodule F b) ∧
        literalGroupLinearConnectionSetShadow F ell ∧
        verticalShearAddEquiv ell ∧
        noOrdinaryUndirectedCayleyCIDefect F

/-- Claim 61322: the arbitrary-function rank-seven ternary quiet-dependency
    assertion through ten projective covector classes and its linear-shear
    connection-set consequence. -/
def claim61322 : Prop :=
  quietDependencyTheorem ∧
    rankSevenQuietClassCorollary

end

end MathlibPlus.Open.Research.CIElementaryAbelian3Rank7GaleShadowClaim61322
