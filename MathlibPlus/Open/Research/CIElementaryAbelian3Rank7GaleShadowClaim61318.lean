import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.CIElementaryAbelian3Rank7GaleShadow

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

def isAddSubgroupSet {H : Type*} [AddCommGroup H] (S : Set H) : Prop :=
  0 ∈ S ∧
    (∀ x y, x ∈ S → y ∈ S → x + y ∈ S) ∧
    (∀ x, x ∈ S → -x ∈ S)

def restrictionIsAdditive (F : B → A) (u : Covector) : Prop :=
  scalarComponent F u 0 = 0 ∧
    ∀ x y : B, x ∈ quietDirections F u → y ∈ quietDirections F u →
      scalarComponent F u (x + y) =
        scalarComponent F u x + scalarComponent F u y

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

def quietSubgroupAndAdditivity : Prop :=
  ∀ (F : B → A), F 0 = 0 →
    ∀ u : Covector, u ≠ 0 →
      isAddSubgroupSet (quietDirections F u) ∧
        restrictionIsAdditive F u

def quietDependencyTheorem : Prop :=
  ∀ (F : B → A), F 0 = 0 →
    ∀ m : ℕ, m ≤ 7 →
      ∀ (u : Fin m → Covector) (d : Fin m → B),
        quietDependencyConditions F m u d →
          quietDependencySlopeSum F m u d = 0

def projectiveClass (u : Covector) : Set Covector :=
  {v | ∃ c : F3, c ≠ 0 ∧ v = c • u}

def projectiveQuietClasses (F : B → A) : Set (Set Covector) :=
  {C | ∃ u : Covector, u ≠ 0 ∧ C = projectiveClass u ∧
    quietDirections F u ≠ ({0} : Set B)}

noncomputable def atMostSevenQuietProjectiveClasses (F : B → A) : Prop :=
  Set.ncard (projectiveQuietClasses F) ≤ 7

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

def linearShearTransportProperties (ell : B →ₗ[F3] A) : Prop :=
  ∀ S : Set V,
    (identityFree S ↔
      identityFree (linearShear ell '' S)) ∧
    (inverseClosed S ↔
      inverseClosed (linearShear ell '' S))

def shearNotUndirectedCayleyCIDefect
    (F : B → A) (ell : B →ₗ[F3] A) : Prop :=
  verticalShearAddEquiv ell ∧
    ∀ (S T : Set V),
      identityFree S →
      identityFree T →
      inverseClosed S →
      inverseClosed T →
      directedCayleyRelationIso (qShear F) S T →
      linearShear ell '' S = T →
        ¬ ordinaryUndirectedCayleyCIDefect S T (qShear F)

def rankSevenQuietClassCorollary : Prop :=
  ∀ (F : B → A), F 0 = 0 →
    atMostSevenQuietProjectiveClasses F →
      ∃ ell : B →ₗ[F3] A,
        (∀ b : B,
          F b - ell b ∈ displacementSubmodule F b) ∧
        (∀ S T : Set V,
          directedCayleyRelationIso (qShear F) S T →
            linearShear ell '' S = T) ∧
        verticalShearAddEquiv ell ∧
        linearShearTransportProperties ell ∧
        shearNotUndirectedCayleyCIDefect F ell

/-- Claim 61318: the arbitrary-function rank-seven ternary quiet-dependency theorem
and its seven-projective-class linear-shear connection-set consequence. -/
def claim61318 : Prop :=
  quietSubgroupAndAdditivity ∧
    quietDependencyTheorem ∧
    rankSevenQuietClassCorollary

end MathlibPlus.Open.Research.CIElementaryAbelian3Rank7GaleShadow
