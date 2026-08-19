import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.CIElementaryAbelian3Rank6_7Gain15Claim61317

noncomputable section

abbrev F3 := ZMod 3
abbrev Fibre := Fin 5 → F3
abbrev V := F3 × Fibre

/-- The exact base-three index used for the displayed fibre table. -/
def fibreIndex (h : Fibre) : Fin 243 :=
  Fin.ofNat 243
    ((h 0).val + 3 * (h 1).val + 9 * (h 2).val +
      27 * (h 3).val + 81 * (h 4).val)

/-- The inverse base-three decoding convention from the source record. -/
def decodeFibre (i : Fin 243) : Fibre :=
  fun j => ((i.val / 3 ^ j.val) % 3 : F3)

/-- The complete permutation table, in index order. -/
def sigmaTable : Fin 243 → Fin 243 :=
![    (0 : Fin 243), 99, 171, 90, 28, 126, 180, 225, 56, 145, 82, 73,
    19, 64, 110, 54, 46, 10, 209, 38, 164, 27, 20, 65,
    11, 217, 47, 112, 238, 93, 229, 140, 50, 211, 175, 84,
    94, 192, 21, 48, 121, 138, 167, 75, 176, 237, 201, 111,
    57, 183, 228, 174, 4, 104, 224, 186, 125, 152, 168, 107,
    134, 70, 196, 123, 222, 159, 105, 178, 8, 33, 132, 96,
    188, 15, 141, 88, 106, 42, 69, 195, 242, 239, 66, 113,
    59, 185, 12, 148, 85, 212, 32, 131, 95, 122, 221, 158,
    76, 149, 165, 68, 30, 129, 184, 120, 58, 5, 102, 147,
    53, 17, 143, 169, 80, 150, 71, 197, 26, 62, 160, 233,
    179, 6, 78, 133, 206, 116, 16, 142, 161, 79, 43, 89,
    114, 25, 204, 208, 37, 1, 29, 235, 199, 226, 216, 181,
    83, 101, 173, 200, 189, 236, 182, 227, 136, 144, 162, 72,
    18, 63, 190, 218, 153, 117, 124, 223, 51, 215, 151, 170,
    34, 24, 97, 52, 231, 60, 7, 213, 177, 98, 35, 240,
    61, 187, 232, 44, 87, 214, 241, 205, 115, 146, 2, 74,
    128, 92, 108, 55, 155, 119, 207, 36, 81, 109, 234, 198,
    9, 137, 45, 163, 100, 172, 91, 191, 127, 154, 118, 135,
    67, 193, 22, 49, 13, 139, 86, 210, 40, 23, 202, 194,
    219, 156, 14, 41, 166, 77, 31, 130, 203, 230, 220, 157,
    103, 39, 3]

/-- The complete gain table, in index order. -/
def correctionTable : Fin 243 → F3 :=
![    (0 : F3), 2, 1, 1, 0, 2, 2, 1, 0, 1, 0, 2,
    2, 1, 0, 0, 2, 1, 2, 1, 0, 0, 2, 1,
    1, 0, 2, 0, 2, 1, 1, 0, 2, 2, 1, 0,
    1, 0, 2, 2, 1, 0, 0, 2, 1, 2, 1, 0,
    0, 2, 1, 1, 0, 2, 0, 2, 1, 1, 0, 2,
    2, 1, 0, 1, 0, 2, 2, 1, 0, 0, 2, 1,
    2, 1, 0, 0, 2, 1, 1, 0, 2, 0, 2, 1,
    1, 0, 2, 2, 1, 0, 1, 0, 2, 2, 1, 0,
    0, 2, 1, 2, 1, 0, 0, 2, 1, 1, 0, 2,
    0, 2, 1, 1, 0, 2, 2, 1, 0, 1, 0, 2,
    2, 1, 0, 0, 2, 1, 2, 1, 0, 0, 2, 1,
    1, 0, 2, 0, 2, 1, 1, 0, 2, 2, 1, 0,
    1, 0, 2, 2, 1, 0, 0, 2, 1, 2, 1, 0,
    0, 2, 1, 1, 0, 2, 0, 2, 1, 1, 0, 2,
    2, 1, 0, 1, 0, 2, 2, 1, 0, 0, 2, 1,
    2, 1, 0, 0, 2, 1, 1, 0, 2, 0, 2, 1,
    1, 0, 2, 2, 1, 0, 1, 0, 2, 2, 1, 0,
    0, 2, 1, 2, 1, 0, 0, 2, 1, 1, 0, 2,
    0, 2, 1, 1, 0, 2, 2, 1, 0, 1, 0, 2,
    2, 1, 0, 0, 2, 1, 2, 1, 0, 0, 2, 1,
    1, 0, 2]

/-- The displayed pointed rank-six permutation. -/
def gain15Permutation : V → V :=
  fun x =>
    (x.1 + correctionTable (fibreIndex x.2),
      decodeFibre (sigmaTable (fibreIndex x.2)))

/-- An ordinary inverse direction, represented by its exact signed pair. -/
def Direction : Type :=
  {D : Finset V // ∃ a : V, a ≠ 0 ∧ D = {a, -a}}

abbrev IncidenceVertex := Direction ⊕ Direction

/-- The source-to-target inverse-direction incidence relation of `q`. -/
def directionIncidence (A B : Direction) : Prop :=
  ∃ x : V, ∃ a : V,
    a ∈ A.1 ∧ gain15Permutation (x + a) - gain15Permutation x ∈ B.1

/-- The bipartite inverse-direction incidence graph. -/
def incidenceAdjacency : IncidenceVertex → IncidenceVertex → Prop
  | Sum.inl A, Sum.inr B => directionIncidence A B
  | Sum.inr B, Sum.inl A => directionIncidence A B
  | _, _ => False

def incidenceGraph : SimpleGraph IncidenceVertex :=
  SimpleGraph.fromRel incidenceAdjacency

abbrev IncidenceComponent := incidenceGraph.ConnectedComponent

def sourceDirections (C : IncidenceComponent) : Set Direction :=
  {A | Sum.inl A ∈ C.supp}

def targetDirections (C : IncidenceComponent) : Set Direction :=
  {B | Sum.inr B ∈ C.supp}

def sourceSize (C : IncidenceComponent) : ℕ :=
  Nat.card {A : Direction // Sum.inl A ∈ C.supp}

def targetSize (C : IncidenceComponent) : ℕ :=
  Nat.card {B : Direction // Sum.inr B ∈ C.supp}

/-- The setwise image of an inverse direction under a linear automorphism. -/
def linearDirectionImage (L : V ≃ₗ[F3] V) (A : Direction) : Set V :=
  L '' (A.1 : Set V)

/-- The signed source and target connection sets of a component collection. -/
def sourceConnectionSet (K : Finset IncidenceComponent) : Set V :=
  {a | ∃ C : IncidenceComponent, C ∈ K ∧
    ∃ A : Direction, A ∈ sourceDirections C ∧ a ∈ A.1}

def targetConnectionSet (K : Finset IncidenceComponent) : Set V :=
  {b | ∃ C : IncidenceComponent, C ∈ K ∧
    ∃ B : Direction, B ∈ targetDirections C ∧ b ∈ B.1}

def identityFree (S : Set V) : Prop :=
  (0 : V) ∉ S

def inverseClosed (S : Set V) : Prop :=
  ∀ ⦃a : V⦄, a ∈ S → -a ∈ S

/-- The ordinary undirected additive Cayley adjacency relation. -/
def cayleyAdjacency (S : Set V) (x y : V) : Prop :=
  x ≠ y ∧ y - x ∈ S

def cayleyIsomorphism (S T : Set V) (f : V → V) : Prop :=
  Function.Bijective f ∧
    ∀ x y : V,
      cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

def ordinaryUndirectedCayleyCIDefect
    (S T : Set V) (f : V → V) : Prop :=
  identityFree S ∧ identityFree T ∧
    inverseClosed S ∧ inverseClosed T ∧
    cayleyIsomorphism S T f ∧
    ¬ ∃ L : V ≃ₗ[F3] V, L '' S = T

/-- The exact fifteen-component all-fusions shadow theorem from Claim 61317.

The direction carrier is the concrete signed-pair realization of
`(F₃⁶ \ {0})/(a ~ -a)`.  Quantifying over all finite subsets of the
fifteen connected components is the literal `2^15` fusion family. -/
def claim61317 : Prop :=
  Fintype.card V = 729 ∧
    Function.Bijective sigmaTable ∧
    sigmaTable 0 = 0 ∧
    correctionTable 0 = 0 ∧
    Function.Bijective gain15Permutation ∧
    gain15Permutation 0 = 0 ∧
    Nat.card Direction = 364 ∧
    Nat.card IncidenceComponent = 15 ∧
    (∀ C : IncidenceComponent, sourceSize C = targetSize C) ∧
    Nat.card {C : IncidenceComponent //
      sourceSize C = 1 ∧ targetSize C = 1} = 1 ∧
    Nat.card {C : IncidenceComponent //
      sourceSize C = 13 ∧ targetSize C = 13} = 1 ∧
    Nat.card {C : IncidenceComponent //
      sourceSize C = 26 ∧ targetSize C = 26} = 1 ∧
    Nat.card {C : IncidenceComponent //
      sourceSize C = 27 ∧ targetSize C = 27} = 12 ∧
    ∃ L : V ≃ₗ[F3] V,
      (∀ C : IncidenceComponent,
        ∀ B : Direction,
          B ∈ targetDirections C ↔
            ∃ A : Direction, A ∈ sourceDirections C ∧
              linearDirectionImage L A = (B.1 : Set V)) ∧
      ∀ K : Finset IncidenceComponent,
        let S := sourceConnectionSet K
        let T := targetConnectionSet K
        inverseClosed S ∧ identityFree S ∧
          inverseClosed T ∧ identityFree T ∧
          cayleyIsomorphism S T gain15Permutation ∧
          L '' S = T ∧
          ¬ ordinaryUndirectedCayleyCIDefect S T gain15Permutation

end
end MathlibPlus.Open.Research.CIElementaryAbelian3Rank6_7Gain15Claim61317
