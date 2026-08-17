import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0783

abbrev CavityRing (n : ℕ) := MvPolynomial (Fin (n + 1)) ℚ
abbrev LowerCavityRing (n : ℕ) := MvPolynomial (Fin n) ℚ

def largestCavityVariable (n : ℕ) : Fin (n + 1) :=
  ⟨n, Nat.lt_succ_self n⟩

def lowerCavityEmbedding (n : ℕ) :
    LowerCavityRing n →ₐ[ℚ] CavityRing n :=
  MvPolynomial.rename (Fin.castLE (Nat.le_succ n))

def treeClosureShape {n : ℕ} (p : CavityRing n) : Prop :=
  ∃ h : LowerCavityRing n,
    p = MvPolynomial.X (largestCavityVariable n) +
      lowerCavityEmbedding n h

def lowerCavityToQuotient {n : ℕ} (p : CavityRing n) :
    LowerCavityRing n →+*
      CavityRing n ⧸ Ideal.span ({p} : Set (CavityRing n)) :=
  (Ideal.Quotient.mk (Ideal.span ({p} : Set (CavityRing n)))).comp
    (lowerCavityEmbedding n).toRingHom

def collarFactor {n e : ℕ} (p : CavityRing n)
    (B : Fin e → CavityRing n)
    (Q : Fin e → Polynomial (CavityRing n)) (a : Fin e) :
    Polynomial (CavityRing n) :=
  Polynomial.C p + Polynomial.X * Polynomial.C (B a) +
    Polynomial.X ^ 2 * Q a

def collarProduct {n e : ℕ} (p : CavityRing n)
    (B : Fin e → CavityRing n)
    (Q : Fin e → Polynomial (CavityRing n))
    (H : Polynomial (CavityRing n)) : Polynomial (CavityRing n) :=
  H * ∏ a : Fin e, collarFactor p B Q a

def elementaryCavity {R : Type*} [CommRing R] {e : ℕ}
    (B : Fin e → R) (k : ℕ) : R :=
  (Finset.univ.filter (fun S : Finset (Fin e) => S.card = k)).sum
    (fun S => S.prod B)

def cavityCharacteristic {R : Type*} [CommRing R] {e : ℕ}
    (B : Fin e → R) : Polynomial R :=
  ∏ a : Fin e, (Polynomial.X - Polynomial.C (B a))

def cavityMultiset {R : Type*} [CommRing R] {e : ℕ}
    (B : Fin e → R) : Multiset R :=
  Multiset.map B (Finset.univ : Finset (Fin e)).1

def collarSetup {n e : ℕ} (p : CavityRing n)
    (B : Fin e → CavityRing n)
    (Q : Fin e → Polynomial (CavityRing n))
    (H P : Polynomial (CavityRing n)) (L : CavityRing n) : Prop :=
  Irreducible p ∧
    H.coeff 0 = L ∧
      P = collarProduct p B Q H ∧
        ¬ p ∣ L

def collarContext {n e : ℕ} (p L : CavityRing n)
    (B C : Fin e → CavityRing n)
    (Q Q' : Fin e → Polynomial (CavityRing n))
    (H H' P P' : Polynomial (CavityRing n)) : Prop :=
  treeClosureShape p ∧
    collarSetup p B Q H P L ∧
      collarSetup p C Q' H' P' L

def exposedResiduesAgree {n e : ℕ} (p : CavityRing n)
    (P P' : Polynomial (CavityRing n)) : Prop :=
  ∀ k : ℕ, k ≤ e →
    ∃ q q' : CavityRing n,
      P.coeff k = p ^ (e - k) * q ∧
        P'.coeff k = p ^ (e - k) * q' ∧
          Ideal.Quotient.mk (Ideal.span ({p} : Set (CavityRing n))) q =
            Ideal.Quotient.mk (Ideal.span ({p} : Set (CavityRing n))) q'

def recoveredCavityData {R : Type*} [CommRing R] {e : ℕ}
    (B C : Fin e → R) : Prop :=
  (∀ k : ℕ, k ≤ e → elementaryCavity B k = elementaryCavity C k) ∧
    cavityCharacteristic B = cavityCharacteristic C ∧
      cavityMultiset B = cavityMultiset C

/-- Equality of the exact exposed prime-adic residues through layer e
 recovers every elementary cavity statistic and the complete
 multiplicity-sensitive characteristic polynomial. -/
def completeCavityCharacteristicRecovery_claim24662 : Prop :=
  ∀ {n e : ℕ} (p L : CavityRing n)
    (B C : Fin e → LowerCavityRing n)
    (Q Q' : Fin e → Polynomial (CavityRing n))
    (H H' P P' : Polynomial (CavityRing n)),
    collarContext p L
      (fun a => lowerCavityEmbedding n (B a))
      (fun a => lowerCavityEmbedding n (C a))
      Q Q' H H' P P' →
      exposedResiduesAgree (e := e) p P P' →
        recoveredCavityData B C

/-- Degree zero together with the first e positive collar coefficients is a
 finite visible width that determines the complete cavity multiset. -/
def finiteVisibleCollarWidth_claim24663 : Prop :=
  ∀ {n e : ℕ} (p L : CavityRing n)
    (B C : Fin e → LowerCavityRing n)
    (Q Q' : Fin e → Polynomial (CavityRing n))
    (H H' P P' : Polynomial (CavityRing n)),
    collarContext p L
      (fun a => lowerCavityEmbedding n (B a))
      (fun a => lowerCavityEmbedding n (C a))
      Q Q' H H' P P' →
      (P.coeff 0 = P'.coeff 0 ∧
        (∀ k : ℕ, 0 < k → k ≤ e → P.coeff k = P'.coeff k)) →
          recoveredCavityData B C

end MathlibPlus.Open.ResearchFormalization.R0783
