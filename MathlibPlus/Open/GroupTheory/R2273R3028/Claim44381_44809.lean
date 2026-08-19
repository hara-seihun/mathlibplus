import Mathlib

namespace MathlibPlus.GroupTheory.R2273R3028

noncomputable section

abbrev ProfileDomain := Fin 11 × Fin 4
abbrev C5 := ZMod 5
abbrev TransversePoint := Fin 11 × C5 × Fin 4

noncomputable def profileSupport (ψ : Fin 11 → Fin 4 → C5) : Finset ProfileDomain :=
  (Finset.univ.product Finset.univ).filter (fun u => ψ u.1 u.2 ≠ 0)

noncomputable def normalizedTransverseProfileSet : Finset (Fin 11 → Fin 4 → C5) :=
  Finset.univ.filter (fun ψ =>
    ψ 0 0 = 0 ∧ (profileSupport ψ).card = 3)

noncomputable def triangularMap
    (ψ : Fin 11 → Fin 4 → C5) : TransversePoint → TransversePoint :=
  fun z => (z.1, z.2.1 + ψ z.1 z.2.2, z.2.2)

/-- Claim 44381: the normalized transverse triangular maps have exactly three
nonzero profile positions away from `(0,0)`, with values in `C5*`, and the
resulting raw family has the stated exact cardinality. -/
def normalizedTransverseTriangularProfileCount_claim44381 : Prop :=
  normalizedTransverseProfileSet.card = 789824 ∧
    (∀ ψ ∈ normalizedTransverseProfileSet,
      ψ 0 0 = 0 ∧
        (profileSupport ψ).card = 3 ∧
        (∀ u : ProfileDomain, u ∈ profileSupport ψ → ψ u.1 u.2 ≠ 0) ∧
        triangularMap ψ (0, 0, 0) = (0, 0, 0)) ∧
    789824 = Nat.choose 43 3 * 4 ^ 3

abbrev CubeVector (d : ℕ) := Fin d → ZMod 2
abbrev DihCarrier (d : ℕ) := CubeVector d × ZMod 2
abbrev ProductVector (d : ℕ) := Fin (d + 1) → ZMod 2

def dihMultiplication (d : ℕ) : DihCarrier d → DihCarrier d → DihCarrier d :=
  fun a b =>
    (a.1 + (if a.2 = 0 then b.1 else -b.1), a.2 + b.2)

noncomputable def dihToProduct (d : ℕ) : DihCarrier d → ProductVector d :=
  fun a => Fin.snoc a.1 a.2

noncomputable def productToDih (d : ℕ) : ProductVector d → DihCarrier d :=
  fun z => (Fin.init z, z (Fin.last d))

/-- Claim 44809: over `C₂^d`, inversion is the identity, so the displayed
semidirect multiplication is coordinatewise addition and the explicit
`Fin.snoc`/`Fin.init` maps give the product `C₂^(d+1)`. -/
def generalizedDihedralC2IsProduct_claim44809 : Prop :=
  ∀ d : ℕ,
    (∀ x : CubeVector d, -x = x) ∧
      (∀ a b : DihCarrier d,
        dihMultiplication d a b = (a.1 + b.1, a.2 + b.2)) ∧
      (∀ a : DihCarrier d, productToDih d (dihToProduct d a) = a) ∧
      (∀ z : ProductVector d, dihToProduct d (productToDih d z) = z) ∧
      (∀ a b : DihCarrier d,
        dihToProduct d (dihMultiplication d a b) =
          dihToProduct d a + dihToProduct d b)

end

end MathlibPlus.GroupTheory.R2273R3028
