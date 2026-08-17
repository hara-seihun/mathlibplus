import Mathlib

namespace MathlibPlus.Open.R1578

open scoped BigOperators
noncomputable section

private abbrev F2 := ZMod 2
private abbrev Arm := Fin 4

private def armExponent (A : Arm → ℕ) (i : Arm) : ℕ := A i + 1

private def totalExponent (A : Arm → ℕ) : ℕ :=
  ∑ i : Arm, armExponent A i

private def singletonPolynomial (A : Arm → ℕ) : Polynomial F2 :=
  ∑ i : Arm, Polynomial.X ^ armExponent A i

private def productPolynomial (A : Arm → ℕ) : Polynomial F2 :=
  ∏ i : Arm, (1 + Polynomial.X ^ armExponent A i)

private def eTwo (A : Arm → ℕ) : Polynomial F2 := by
  classical
  exact ∑ I ∈ (Finset.univ : Finset (Finset Arm)).filter
      (fun I => I.card = 2),
    ∏ i ∈ I, Polynomial.X ^ armExponent A i

private def eThree (A : Arm → ℕ) : Polynomial F2 := by
  classical
  exact ∑ I ∈ (Finset.univ : Finset (Finset Arm)).filter
      (fun I => I.card = 3),
    ∏ i ∈ I, Polynomial.X ^ armExponent A i

private def armWeight (A : Arm → ℕ) : ℕ :=
  ∑ i : Arm, A i

private def armF (a : ℕ) : Polynomial F2 :=
  ∑ k ∈ Finset.Icc 1 a,
    Polynomial.C ((a - k + 1 : ℕ) : F2) * Polynomial.X ^ k

private def armJ (a : ℕ) : Polynomial F2 :=
  ∑ k ∈ Finset.range (a + 1), Polynomial.X ^ k

private def connectedSpiderPolynomial (A : Arm → ℕ) : Polynomial F2 :=
  (∑ i : Arm, armF (A i)) +
    Polynomial.X * ∏ i : Arm, armJ (A i)

private def KPolynomial (A : Arm → ℕ) : Polynomial F2 :=
  productPolynomial A + (1 + Polynomial.X ^ 2) * singletonPolynomial A

private def GPolynomial (A : Arm → ℕ) : Polynomial F2 :=
  KPolynomial A + 1 + Polynomial.X ^ totalExponent A

private def reciprocalShift (shift : ℕ) (f : Polynomial F2) : Polynomial F2 := by
  classical
  exact ∑ n ∈ f.support,
    Polynomial.C (f.coeff n) * Polynomial.X ^ (shift - n)

private def foldedSingletonExponents
    (A : Arm → ℕ) : Multiset ℕ :=
  (Finset.univ : Finset Arm).1.map
    (fun i => min (armExponent A i)
      (totalExponent A - 2 - armExponent A i))

/-- Claim 39334: reciprocal symmetrization recovers the pair-sum term and
retains all three reciprocal identities, without an equal-total hypothesis. -/
def claim39334 : Prop :=
  ∀ A : Arm → ℕ,
    reciprocalShift (totalExponent A + 2)
        (Polynomial.X ^ 2 * singletonPolynomial A) = eThree A ∧
    reciprocalShift (totalExponent A + 2) (eThree A) =
      Polynomial.X ^ 2 * singletonPolynomial A ∧
    reciprocalShift (totalExponent A + 2) (eTwo A) =
      Polynomial.X ^ 2 * eTwo A ∧
    eTwo A =
      (GPolynomial A +
        reciprocalShift (totalExponent A + 2) (GPolynomial A)) /
        (1 + Polynomial.X ^ 2) ∧
    (∀ A' : Arm → ℕ,
      KPolynomial A = KPolynomial A' →
        eTwo A = eTwo A')




end

end MathlibPlus.Open.R1578
