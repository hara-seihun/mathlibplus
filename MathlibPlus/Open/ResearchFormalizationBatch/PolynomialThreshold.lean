import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

abbrev complexPolynomial := Polynomial ℂ

def castIntegerPolynomial (p : Polynomial ℤ) : complexPolynomial :=
  p.map (Int.castRingHom ℂ)

noncomputable def mahlerMeasure (p : complexPolynomial) : ℝ :=
  (p.roots.map (fun z => max (1 : ℝ) ‖z‖)).prod

noncomputable def exteriorRootCount (p : complexPolynomial) : ℕ :=
  (p.roots.filter (fun z => (1 : ℝ) < ‖z‖)).card

noncomputable def exteriorRootProduct (p : Polynomial ℤ) : ℂ :=
  ((castIntegerPolynomial p).roots.filter (fun z => (1 : ℝ) < ‖z‖)).prod

def nonCyclotomicInteger (p : Polynomial ℤ) : Prop :=
  ∀ n : ℕ, p ≠ Polynomial.cyclotomic n ℤ

def reciprocalQuartic (a b : ℤ) : complexPolynomial :=
  Polynomial.X ^ 4 + Polynomial.C (a : ℂ) * Polynomial.X ^ 3 +
    Polynomial.C (b : ℂ) * Polynomial.X ^ 2 +
    Polynomial.C (a : ℂ) * Polynomial.X + 1

def reciprocalSextic (a b c : ℤ) : complexPolynomial :=
  Polynomial.X ^ 6 + Polynomial.C (a : ℂ) * Polynomial.X ^ 5 +
    Polynomial.C (b : ℂ) * Polynomial.X ^ 4 + Polynomial.C (c : ℂ) * Polynomial.X ^ 3 +
    Polynomial.C (b : ℂ) * Polynomial.X ^ 2 + Polynomial.C (a : ℂ) * Polynomial.X + 1

def claim45956 : Prop :=
  ∀ p : Polynomial ℤ,
    p.IsPrimitive ∧ Irreducible p ∧ p.Monic ∧ p.reverse = p ∧
      nonCyclotomicInteger p ∧
      exteriorRootCount (castIntegerPolynomial p) = 2 ∧
      (minpoly ℚ (exteriorRootProduct p)).reverse ≠ minpoly ℚ (exteriorRootProduct p) →
    (1177 / 1000 : ℝ) ≤ mahlerMeasure (castIntegerPolynomial p)

def claim45958 : Prop :=
  (∀ (d : ℕ) (p : complexPolynomial),
    p.Monic → p.natDegree = d →
      ∀ k : ℕ, k ≤ d →
        ‖p.coeff (d - k)‖ ≤
          (Nat.choose d k : ℝ) * mahlerMeasure p) ∧
  (∀ a b : ℤ,
    mahlerMeasure (reciprocalQuartic a b) < (1177 / 1000 : ℝ) →
      ‖(a : ℝ)‖ ≤ 4 ∧ ‖(b : ℝ)‖ ≤ 7) ∧
  (∀ a b c : ℤ,
    mahlerMeasure (reciprocalSextic a b c) < (1177 / 1000 : ℝ) →
      ‖(a : ℝ)‖ ≤ 7 ∧ ‖(b : ℝ)‖ ≤ 17 ∧ ‖(c : ℝ)‖ ≤ 23)

def quarticTraceForm (a b : ℂ) : complexPolynomial :=
  Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C (b - 2)

def sexticTraceForm (a b c : ℂ) : complexPolynomial :=
  Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 +
    Polynomial.C (b - 3) * Polynomial.X + Polynomial.C (c - 2 * a)

def IsTraceRepresentation (P Q : complexPolynomial) (n : ℕ) : Prop :=
  P.natDegree = 2 * n ∧
    ∀ x : ℂ, x ≠ 0 →
      Polynomial.eval x P = x ^ n * Polynomial.eval (x + x⁻¹) Q

noncomputable def realRootCountBetween (Q : complexPolynomial)
    (lo hi : ℝ) : ℕ :=
  (Q.roots.filter (fun z => z.im = 0 ∧ lo < z.re ∧ z.re < hi)).card

noncomputable def exactSturmInteriorCount (Q : complexPolynomial) : ℕ :=
  realRootCountBetween Q (-2) 2

def claim45959 : Prop :=
  (∀ P Q : complexPolynomial,
    P.Monic → P.natDegree = 4 → P.reverse = P →
      IsTraceRepresentation P Q 2 →
      Q = quarticTraceForm (P.coeff 3) (P.coeff 2)) ∧
  (∀ P Q : complexPolynomial,
    P.Monic → P.natDegree = 6 → P.reverse = P →
      IsTraceRepresentation P Q 3 →
      Q = sexticTraceForm (P.coeff 5) (P.coeff 4) (P.coeff 3)) ∧
  (∀ n : ℕ, ∀ P Q : complexPolynomial,
    P.Monic → P.natDegree = 2 * n → P.reverse = P →
      IsTraceRepresentation P Q n →
      Polynomial.eval (2 : ℂ) Q ≠ 0 →
      Polynomial.eval (-2 : ℂ) Q ≠ 0 →
      exteriorRootCount P = Q.natDegree - exactSturmInteriorCount Q)

end
end MathlibPlus.Open.ResearchFormalizationBatch
