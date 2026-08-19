import MathlibPlus.Open.Algebra.NewResearch2.C0112Repair

namespace MathlibPlus.Open.Algebra.NewResearch2.C0112Claim1738

open scoped BigOperators
open MathlibPlus.Open.Algebra.NewResearch2.C0112Repair

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev Row (d : ℕ) := {K : Fin d → ℕ // K ∈ admissibleRows d}
abbrev Matching (d : ℕ) := {M : Equiv.Perm (Fin (2 * d + 2)) // M ∈ matchingCandidates d}

private def listLexNat (xs ys : List ℕ) : Prop :=
  List.Lex (fun a b : ℕ => a < b) xs ys

private def rowBefore {d : ℕ} (K L : Fin d → ℕ) : Prop :=
  (∑ i : Fin d, K i) < ∑ i : Fin d, L i ∨
    ((∑ i : Fin d, K i) = ∑ i : Fin d, L i ∧
      listLexNat (List.ofFn K) (List.ofFn L))

private def endpointList (B : Finset ℕ) : List ℕ :=
  B.sort (fun a b : ℕ => a ≤ b)

private def matchingBefore {d : ℕ}
    (M N : Equiv.Perm (Fin (2 * d + 2))) : Prop :=
  let BM := leftEndpointSet d M
  let BN := leftEndpointSet d N
  (BM.sum id < BN.sum id) ∨
    (BM.sum id = BN.sum id ∧
      listLexNat (endpointList BM) (endpointList BN))

private def cupMatrix (d : ℕ) : Matrix (Row d) (Row d) ℚ :=
  fun K L => cupIncidence d K.1 (canonicalMatching d L.1)

private def cupInverseEquation {d : ℕ}
    (W Winv : Matrix (Row d) (Row d) ℚ) : Prop :=
  W * Winv = 1 ∧ Winv * W = 1

private def cupRhs (d : ℕ) (a : Polynomial ℚ) (K : Row d) : Polynomial ℚ :=
  Polynomial.C (rowGauge d K.1) * flaggedMinor a d K.1

private def cupCoordinateFromInverse {d : ℕ}
    (Winv : Matrix (Row d) (Row d) ℚ)
    (a : Polynomial ℚ) (K : Row d) : Polynomial ℚ :=
  ∑ L : Row d, (Winv K L) • cupRhs d a L

private def canonicalPartitionCoordinate {d : ℕ}
    (Winv : Matrix (Row d) (Row d) ℚ)
    (a : Polynomial ℚ) (part : Fin d → ℕ)
    (hpart : partitionRowSet d part ∈ admissibleRows d) : Polynomial ℚ :=
  cupCoordinateFromInverse Winv a ⟨partitionRowSet d part, hpart⟩

private def matchingRowCorrespondence (d : ℕ) : Prop :=
  ∀ M : Matching d, ∃! K : Row d,
    leftEndpointSet d M.1 = associatedEndpointSet d K.1

private def orderedCupFrame (d : ℕ) : Prop :=
  (∀ K L : Row d,
    rowBefore K.1 L.1 ↔
      matchingBefore (canonicalMatching d K.1)
        (canonicalMatching d L.1)) ∧
    matchingRowCorrespondence d

/-- Claim 1738: the exact area-then-endpoint-lex Catalan ordering gives the
lower-unitriangular gauged cup matrix, whose inverse supplies the cup
coordinates and the canonical partition coordinates. -/
def lowerUnitriangularCupCoordinates_claim1738 : Prop :=
  ∀ d : ℕ,
    ∃ Winv : Matrix (Row d) (Row d) ℚ,
      orderedCupFrame d ∧
        (∀ K L : Row d,
          rowBefore K.1 L.1 → cupMatrix d K L = 0) ∧
          (∀ K : Row d, cupMatrix d K K = 1) ∧
            cupInverseEquation (cupMatrix d) Winv ∧
              (∀ a : Polynomial ℚ, ∀ K : Row d,
                ∃! α : Row d → Polynomial ℚ,
                  (∀ L : Row d,
                    (∑ J : Row d,
                      (cupMatrix d L J) • α J) = cupRhs d a L) ∧
                    (∀ L : Row d,
                      α L = cupCoordinateFromInverse Winv a L) ∧
                      α K = cupCoordinateFromInverse Winv a K) ∧
                (∀ (part : Fin d → ℕ)
                    (hpart : partitionRowSet d part ∈ admissibleRows d)
                    (a : Polynomial ℚ),
                  canonicalPartitionCoordinate Winv a part hpart =
                    cupCoordinateFromInverse Winv a
                      ⟨partitionRowSet d part, hpart⟩)

end

end MathlibPlus.Open.Algebra.NewResearch2.C0112Claim1738
