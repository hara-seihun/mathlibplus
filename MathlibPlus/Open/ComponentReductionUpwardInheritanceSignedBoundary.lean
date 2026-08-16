import Mathlib
import MathlibPlus.Open.CayleyCI.FormalizationBatch

namespace MathlibPlus.Open

open Set
open MathlibPlus.Open.CayleyCI

/-- An ordinary identity-free inverse-closed additive connection set. -/
def additiveConnectionSet {G : Type*} [AddGroup G]
    (S : Set G) : Prop :=
  AddIdentityFreeInverseClosed G S

/-- Additive Cayley adjacency on possibly different carriers. -/
def additiveCayleyAdjacency {G : Type*} [AddGroup G]
    (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

def additiveCayleyGraphIso
    {G H : Type*} [AddGroup G] [AddGroup H]
    (S : Set G) (T : Set H) (e : G ≃ H) : Prop :=
  ∀ x y,
    additiveCayleyAdjacency S x y ↔
      additiveCayleyAdjacency T (e x) (e y)

/-- Existence of an ordinary additive Cayley-graph isomorphism. -/
def additiveCayleyGraphsIsomorphic
    {G H : Type*} [AddGroup G] [AddGroup H]
    (S : Set G) (T : Set H) : Prop :=
  ∃ e : G ≃ H, additiveCayleyGraphIso S T e

/-- A linear transporter of two connection sets. -/
def linearTransporter (F : Type*) {G H : Type*} [Semiring F]
    [AddCommGroup G] [AddCommGroup H]
    [Module F G] [Module F H]
    (S : Set G) (T : Set H) : Prop :=
  ∃ e : G ≃ₗ[F] H, Set.image e S = T

/-- A connected defect on two finite-dimensional additive vector spaces. -/
def connectedCayleyDefect (p : ℕ)
    {G H : Type*} [Fact (Nat.Prime p)]
    [AddCommGroup G] [AddCommGroup H]
    [Module (ZMod p) G] [Module (ZMod p) H]
    [FiniteDimensional (ZMod p) G]
    [FiniteDimensional (ZMod p) H]
    (S : Set G) (T : Set H) : Prop :=
  additiveConnectionSet S ∧
    additiveConnectionSet T ∧
      Submodule.span (ZMod p) S = ⊤ ∧
        Submodule.span (ZMod p) T = ⊤ ∧
          additiveCayleyGraphsIsomorphic S T ∧
            ¬ linearTransporter (ZMod p) S T

/-- A defect on the coordinate model of `C_p^d`. -/
def elementaryCayleyDefect (p d : ℕ) [Fact (Nat.Prime p)]
    (S T : Set (Fin d → ZMod p)) : Prop :=
  additiveConnectionSet S ∧
    additiveConnectionSet T ∧
      additiveCayleyGraphsIsomorphic S T ∧
        ¬ linearTransporter (ZMod p) S T

/-- Ordinary undirected CI for the coordinate model of `C_p^d`. -/
def elementaryUndirectedCI (p d : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ S T : Set (Fin d → ZMod p),
    additiveConnectionSet S →
      additiveConnectionSet T →
        additiveCayleyGraphsIsomorphic S T →
          linearTransporter (ZMod p) S T

/-- The restriction of a connection set to its span, as a set of span
vectors. -/
def restrictedCayleySet {F G : Type*} [Semiring F]
    [AddCommMonoid G] [Module F G]
    (S : Set G) (U : Submodule F G) : Set U :=
  {u | (u : G) ∈ S}

/-- Adjoin zero coordinates to a vector in the first `d` coordinates. -/
def zeroCoordinatePad {p d n : ℕ} [Fact (Nat.Prime p)]
    (h : d ≤ n) (x : Fin d → ZMod p) : Fin n → ZMod p :=
  fun i => if hi : i.val < d then x ⟨i.val, hi⟩ else 0

/-- The padded connection set. -/
def zeroCoordinatePadSet {p d n : ℕ} [Fact (Nat.Prime p)]
    (h : d ≤ n) (S : Set (Fin d → ZMod p)) : Set (Fin n → ZMod p) :=
  Set.image (zeroCoordinatePad h) S

/-- Component reduction, upward inheritance, and the conditional signed-basis
boundary, with the common paired count obtained from graph isomorphism rather
than assumed in advance. -/
def ComponentReductionUpwardInheritanceSignedBoundary : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)],
    Odd p →
      ∀ (V V' : Type*)
        [AddCommGroup V] [AddCommGroup V']
        [Module (ZMod p) V] [Module (ZMod p) V']
        [FiniteDimensional (ZMod p) V]
        [FiniteDimensional (ZMod p) V']
        [Fintype V] [Fintype V'],
        Module.finrank (ZMod p) V = Module.finrank (ZMod p) V' →
          ∀ S : Set V, ∀ T : Set V',
            additiveConnectionSet S →
              additiveConnectionSet T →
                additiveCayleyGraphsIsomorphic S T →
                  let U := Submodule.span (ZMod p) S
                  let W := Submodule.span (ZMod p) T
                  let m := S.ncard / 2
                  S.ncard = T.ncard ∧
                    S.ncard / 2 = T.ncard / 2 ∧
                      (∀ e : V ≃ V',
                        additiveCayleyGraphIso S T e →
                          Module.finrank (ZMod p) U =
                              Module.finrank (ZMod p) W ∧
                            ∃ f : U ≃ W,
                              f (0 : U) = (0 : W) ∧
                                (∀ x : U,
                                  (f x : V') =
                                    e (x : V) - e (0 : V)) ∧
                                  additiveCayleyGraphIso
                                    (restrictedCayleySet S U)
                                    (restrictedCayleySet T W) f) ∧
                        ((linearTransporter (ZMod p) S T) ↔
                          linearTransporter (ZMod p)
                            (restrictedCayleySet S U)
                            (restrictedCayleySet T W)) ∧
                          (m = Module.finrank (ZMod p) U →
                            linearTransporter (ZMod p) S T) ∧
                            ((¬ linearTransporter (ZMod p) S T) →
                              m ≥ Module.finrank (ZMod p) U + 1) ∧
                              (∀ d n : ℕ, ∀ h : d ≤ n,
                                ∀ A B : Set (Fin d → ZMod p),
                                  elementaryCayleyDefect p d A B →
                                    elementaryCayleyDefect p n
                                      (zeroCoordinatePadSet h A)
                                      (zeroCoordinatePadSet h B)) ∧
                                (∀ d r : ℕ, d ≤ r →
                                  elementaryUndirectedCI p r →
                                    elementaryUndirectedCI p d) ∧
                                  (∀ k : ℕ,
                                    elementaryUndirectedCI p k →
                                      ¬ linearTransporter
                                        (ZMod p) S T →
                                        ∃ d : ℕ,
                                          k + 1 ≤ d ∧
                                            d = Module.finrank
                                              (ZMod p) U ∧
                                              connectedCayleyDefect p
                                                (G := U) (H := W)
                                                (restrictedCayleySet S U)
                                                (restrictedCayleySet T W) ∧
                                              2 * k + 4 ≤ S.ncard) ∧
                                    (elementaryUndirectedCI p 7 →
                                      ¬ linearTransporter
                                        (ZMod p) S T →
                                        8 ≤ Module.finrank
                                          (ZMod p) U ∧
                                          18 ≤ S.ncard)

end MathlibPlus.Open
