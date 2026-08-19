import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIBinaryClaim61040

noncomputable section

abbrev BinaryVector (r : ℕ) := Fin r → ZMod 2
abbrev Group (r : ℕ) := BinaryVector r × ZMod 9

def binaryPlane (r : ℕ) : Set (Group r) :=
  {g | g.2 = 0}

def ninthProjection {r : ℕ} (g : Group r) : ZMod 9 :=
  g.2

def fibrePreimage {r : ℕ} (C : Set (ZMod 9)) : Set (Group r) :=
  {g | ninthProjection g ∈ C}

def completeFibreConnectionSet {r : ℕ} (ε : Fin 2)
    (C : Set (ZMod 9)) : Set (Group r) :=
  if ε.val = 0 then
    fibrePreimage C
  else
    (binaryPlane r \ {0}) ∪ fibrePreimage C

def identityFree {r : ℕ} (S : Set (Group r)) : Prop :=
  (0 : Group r) ∉ S

def inverseClosed {G : Type*} [Neg G] (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

def inverseClosedC (C : Set (ZMod 9)) : Prop :=
  (0 : ZMod 9) ∉ C ∧
    ∀ ⦃c : ZMod 9⦄, c ∈ C → -c ∈ C

def ordinaryCayleyAdjacency {r : ℕ} (S : Set (Group r))
    (x y : Group r) : Prop :=
  x ≠ y ∧ y - x ∈ S

def ordinaryCayleyGraphIsomorphism {r : ℕ}
    (S T : Set (Group r)) : Prop :=
  ∃ e : Group r ≃ Group r,
    ∀ x y : Group r,
      ordinaryCayleyAdjacency S x y ↔
        ordinaryCayleyAdjacency T (e x) (e y)

def ordinaryUndirectedCIConnectionSet {r : ℕ}
    (S : Set (Group r)) : Prop :=
  identityFree S ∧
    inverseClosed S ∧
      ∀ T : Set (Group r),
        identityFree T →
          inverseClosed T →
            ordinaryCayleyGraphIsomorphism S T →
              ∃ α : Group r ≃+ Group r, α '' S = T

/-- Distinct complete-fibre connection sets, so the cardinality counts sets
rather than presentations by `(C, ε)`. -/
abbrev CompleteFibreConnection (r : ℕ) :=
  {S : Set (Group r) //
    ∃ (C : Set (ZMod 9)) (ε : Fin 2),
      inverseClosedC C ∧
        S = completeFibreConnectionSet (r := r) ε C}

/-- Claim 61040: every complete fibre is an ordinary undirected CI set, and at
ranks three, four, and five the exact complete-fibre family has 32 distinct
members, all CI without a valency restriction. -/
def claim61040 : Prop :=
  (∀ (r : ℕ), 1 ≤ r →
    ∀ C : Set (ZMod 9),
      inverseClosedC C →
        ∀ ε : Fin 2,
          ordinaryUndirectedCIConnectionSet
            (completeFibreConnectionSet (r := r) ε C)) ∧
  (∀ (r : ℕ), (r = 3 ∨ r = 4 ∨ r = 5) →
    letI : Fintype (CompleteFibreConnection r) := Fintype.ofFinite _
    Fintype.card (CompleteFibreConnection r) = 32 ∧
      ∀ S : CompleteFibreConnection r,
        ordinaryUndirectedCIConnectionSet S.1)

end
end MathlibPlus.Open.ResearchFormalization.CIBinaryClaim61040
