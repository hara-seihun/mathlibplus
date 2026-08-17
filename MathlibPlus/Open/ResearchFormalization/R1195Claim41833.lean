import Mathlib
import MathlibPlus.Open.ResearchBatchHallControls

namespace MathlibPlus.Open.ResearchFormalization.R1195Claim41833

open MathlibPlus.Open.ResearchBatchHallControls

noncomputable section

/-- Subgroups for the explicitly presented `Gm` operation.  The operation is
kept concrete rather than replaced with an abstract group. -/
def gmSubgroup (m : ℕ) (H : Set (Gm m)) : Prop :=
  gmOne m ∈ H ∧
    (∀ x, x ∈ H → gmInv m x ∈ H) ∧
      (∀ x y, x ∈ H → y ∈ H → gmMul m x y ∈ H)

def gmGenerated (m : ℕ) (S : Set (Gm m)) : Set (Gm m) :=
  {x | ∀ H : Set (Gm m), gmSubgroup m H → S ⊆ H → x ∈ H}

def gmCyclicA (m : ℕ) : Set (Gm m) :=
  gmGenerated m {gmA m}

def gmCommutator (m : ℕ) (x y : Gm m) : Gm m :=
  gmMul m (gmMul m (gmMul m (gmInv m x) (gmInv m y)) x) y

def gmCommutators (m : ℕ) : Set (Gm m) :=
  {z | ∃ x y : Gm m, z = gmCommutator m x y}

def gmDerived (m : ℕ) : Set (Gm m) :=
  gmGenerated m (gmCommutators m)

/-- The cyclic subgroup generated from `a` is explicitly identified with the
additive cyclic model `ZMod m`. -/
def cyclicAIsCm (m : ℕ) : Prop :=
  ∃ e : ZMod m ≃ {x : Gm m // x ∈ gmCyclicA m},
    (e 0).1 = gmOne m ∧
      ∀ x y : ZMod m,
        (e (x + y)).1 = gmMul m (e x).1 (e y).1

def uniqueOrderMSubgroup (m : ℕ) : Prop :=
  ∀ H : Set (Gm m),
    gmSubgroup m H →
      Nat.card {x : Gm m // x ∈ H} = m →
        H = gmCyclicA m

def characteristicOddHallSubgroup (m : ℕ) : Prop :=
  gmCyclicA m = explicitOddHallCarrier m ∧
    gmCyclicA m = oddHallCarrier m ∧
      ∀ φ : Gm m → Gm m, gmAutomorphism m φ →
        φ '' gmCyclicA m = gmCyclicA m

/-- Odd-order subgroups have trivial image under the displayed quotient
projection to `ZMod 8`. -/
def oddSubgroupMapsTrivially (m : ℕ) : Prop :=
  ∀ H : Set (Gm m),
    gmSubgroup m H →
      Odd (Nat.card {x : Gm m // x ∈ H}) →
        ∀ h : Gm m, h ∈ H → h.2 = 0

/-- A concrete first-isomorphism description of the quotient over the odd Hall
subgroup.  The fibres of `q` are precisely its right cosets, and `q` is the
usual second-coordinate projection onto `C₈`. -/
def quotientIsCyclic8 (m : ℕ) : Prop :=
  ∃ q : Gm m → ZMod 8,
    Function.Surjective q ∧
      (∀ g h : Gm m, q (gmMul m g h) = q g + q h) ∧
        (∀ g : Gm m, q g = g.2) ∧
          ∀ g h : Gm m,
            q g = q h ↔
              ∃ k : Gm m, k ∈ gmCyclicA m ∧ gmMul m g k = h

/-- Claim 41833: the displayed `C_m ⋊ C₈` has the commutator/odd-Hall
structure and quotient asserted in the admitted source claim. -/
def claim41833 : Prop :=
  ∀ m : ℕ, Odd m →
    gmGroupAxioms m ∧
      gmPresentationRelations m ∧
        gmDerived m = gmCyclicA m ∧
          cyclicAIsCm m ∧
            uniqueOrderMSubgroup m ∧
              characteristicOddHallSubgroup m ∧
                oddSubgroupMapsTrivially m ∧
                  quotientIsCyclic8 m

end

end MathlibPlus.Open.ResearchFormalization.R1195Claim41833
