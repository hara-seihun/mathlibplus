import Mathlib
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

open scoped BigOperators
open MvPolynomial

namespace MathlibPlus.Open.NewResearch2

noncomputable section

abbrev Poly := Polynomial ℚ
abbrev Frac := FractionRing Poly
abbrev Part4 (d : ℕ) := Fin 4 → Fin (d + 1)
abbrev Part3 (d : ℕ) := Fin 3 → Fin (d + 1)
abbrev Part2 (d : ℕ) := Fin 2 → Fin (d + 1)
abbrev Vertex (d : ℕ) := Fin (2 * d + 2)
abbrev Matching (d : ℕ) := Vertex d → Vertex d

def qconst (q : ℚ) : Poly := Polynomial.C q

def completeHomogeneousEval {R : Type*} [CommSemiring R]
    (s k : ℕ) (a : R) : R :=
  eval₂ (RingHom.id R) (fun i : Fin (s + 2) => a + (i.1 : R))
    (hsymm (Fin (s + 2)) R k)

def flaggedArray {R : Type*} [CommSemiring R]
    (a : R) (s j : ℕ) : R :=
  (s + 1 : R) * if s + 1 ≤ 2 * j then
    completeHomogeneousEval s (2 * j - s - 1) a else 0

def fourK (d : ℕ) (p : Part4 d) (i : Fin d) : ℕ :=
  if i.1 < d - 4 then i.1 else
  if i.1 = d - 4 then d - 4 + (p 3).1 else
  if i.1 = d - 3 then d - 3 + (p 2).1 else
  if i.1 = d - 2 then d - 2 + (p 1).1 else
  if i.1 = d - 1 then d - 1 + (p 0).1 else i.1

def threeK (d : ℕ) (p : Part3 d) (i : Fin d) : ℕ :=
  if i.1 < d - 3 then i.1 else
  if i.1 = d - 3 then d - 3 + (p 2).1 else
  if i.1 = d - 2 then d - 2 + (p 1).1 else
  if i.1 = d - 1 then d - 1 + (p 0).1 else i.1

def twoK (d : ℕ) (p : Part2 d) (i : Fin d) : ℕ :=
  if i.1 < d - 2 then i.1 else
  if i.1 = d - 2 then d - 2 + (p 1).1 else
  if i.1 = d - 1 then d - 1 + (p 0).1 else i.1

def oneK (d : ℕ) (n : Fin (d + 1)) (i : Fin d) : ℕ :=
  if i.1 = d - 1 then d - 1 + n.1 else i.1

def flaggedMinor {R : Type*} [CommRing R]
    (a : R) (d : ℕ) (K : Fin d → ℕ) : R :=
  Matrix.det (fun (i : Fin d) (j : Fin d) => flaggedArray a (K i) (j.1 + 1))

def h4 (d : ℕ) (p : Part4 d) (b : Poly) : Poly :=
  flaggedMinor (b + qconst (1 / 2 : ℚ)) d (fourK d p)
def h3 (d : ℕ) (p : Part3 d) (b : Poly) : Poly :=
  flaggedMinor (b + qconst (1 / 2 : ℚ)) d (threeK d p)
def h2 (d : ℕ) (p : Part2 d) (b : Poly) : Poly :=
  flaggedMinor (b + qconst (1 / 2 : ℚ)) d (twoK d p)
def h1 (d : ℕ) (n : Fin (d + 1)) (b : Poly) : Poly :=
  flaggedMinor (b + qconst (1 / 2 : ℚ)) d (oneK d n)
def h0 (d : ℕ) (b : Poly) : Poly :=
  flaggedMinor (b + qconst (1 / 2 : ℚ)) d (fun i => i.1)

def poch (x : Poly) (k : ℕ) : Poly :=
  Finset.prod (Finset.range k) (fun i => x + qconst (i : ℚ))
def Y (d : ℕ) : Poly := 2 * Polynomial.X + qconst (d + 1 : ℚ)
def principalProduct (d : ℕ) : Poly :=
  (Nat.factorial d : Poly) * Finset.prod (Finset.range (d + 1)) (fun i =>
    Finset.prod (Finset.range (d + 1)) (fun j =>
      if i < j then 2 * Polynomial.X + qconst (i + j + 1 : ℚ) else 1))
def delta11 (d n m : ℕ) : Poly :=
  poch (Y d) n * poch (Y d - 1) m * poch (Y d - 2) 1 * poch (Y d - 3) 1
def delta21 (d n m : ℕ) : Poly :=
  poch (Y d) n * poch (Y d - 1) m * poch (Y d - 2) 2 * poch (Y d - 3) 1

def fourAdmissible (d : ℕ) (p : Part4 d) : Prop :=
  4 ≤ d ∧ Antitone (fun i => (p i).1) ∧
    StrictMono (fourK d p) ∧ ∀ i : Fin d, fourK d p i ≤ 2 * i.1 + 1
def threeAdmissible (d : ℕ) (p : Part3 d) : Prop :=
  4 ≤ d ∧ Antitone (fun i => (p i).1) ∧
    StrictMono (threeK d p) ∧ ∀ i : Fin d, threeK d p i ≤ 2 * i.1 + 1
def twoAdmissible (d : ℕ) (p : Part2 d) : Prop :=
  4 ≤ d ∧ Antitone (fun i => (p i).1) ∧
    StrictMono (twoK d p) ∧ ∀ i : Fin d, twoK d p i ≤ 2 * i.1 + 1

abbrev Poly4 (d : ℕ) := Part4 d → Poly
abbrev Poly3 (d : ℕ) := Part3 d → Poly
abbrev Poly2 (d : ℕ) := Part2 d → Poly

def coeffwiseNonneg (p : Poly) : Prop := ∀ k : ℕ, 0 ≤ p.coeff k
def coeffwisePositive (p : Poly) : Prop :=
  ∀ k : ℕ, p.coeff k ≠ 0 → 0 < p.coeff k
def coeffwiseLe (p q : Poly) : Prop := ∀ k : ℕ, p.coeff k ≤ q.coeff k

def selected (d : ℕ) (K : Fin d → ℕ) (v : Vertex d) : Prop :=
  v.1 = 0 ∨ ∃ i : Fin d, v.1 = K i + 1
def noncrossing (d : ℕ) (M : Matching d) : Prop :=
  ∀ p q r s : Vertex d, p.1 < r.1 → r.1 < q.1 → q.1 < s.1 →
    M p = q → M r = s → False
def cupMatching (d : ℕ) (K : Fin d → ℕ) (M : Matching d) : Prop :=
  (∀ p, M (M p) = p) ∧ (∀ p, M p ≠ p) ∧ noncrossing d M ∧
    (∀ p, selected d K p ↔ ¬ selected d K (M p))
def cupSign (d : ℕ) (K : Fin d → ℕ) (M : Matching d) : ℚ := by
  classical
  exact (-1 : ℚ) ^ (Finset.filter (fun p : Vertex d =>
    p.1 < (M p).1 ∧ selected d K p) Finset.univ).card
def cupEntry (d : ℕ) (row column : Fin d → ℕ) : ℚ := by
  classical
  exact ∑ M : Matching d, if cupMatching d column M then cupSign d row M else 0

def W4 (d : ℕ) (p q : Part4 d) : Poly := qconst (cupEntry d (fourK d p) (fourK d q))
def W3 (d : ℕ) (p q : Part3 d) : Poly := qconst (cupEntry d (threeK d p) (threeK d q))
def W2 (d : ℕ) (p q : Part2 d) : Poly := qconst (cupEntry d (twoK d p) (twoK d q))

def lex3 (p q : Part3 d) : Prop :=
  (p 0).1 < (q 0).1 ∨ ((p 0).1 = (q 0).1 ∧
    ((p 1).1 < (q 1).1 ∨ ((p 1).1 = (q 1).1 ∧ (p 2).1 < (q 2).1)))
def lex2 (p q : Part2 d) : Prop :=
  (p 0).1 < (q 0).1 ∨ ((p 0).1 = (q 0).1 ∧ (p 1).1 < (q 1).1)

def lowerUnitriangular3 (d : ℕ) : Prop :=
  (∀ p q : Part3 d, threeAdmissible d p → threeAdmissible d q → lex3 p q → W3 d p q = 0) ∧
    (∀ p : Part3 d, threeAdmissible d p → W3 d p p = 1)
def lowerUnitriangular2 (d : ℕ) : Prop :=
  (∀ p q : Part2 d, twoAdmissible d p → twoAdmissible d q → lex2 p q → W2 d p q = 0) ∧
    (∀ p : Part2 d, twoAdmissible d p → W2 d p p = 1)

def signedH4 (d : ℕ) (p : Part4 d) (b : Poly) : Poly :=
  (-1 : Poly) ^ (∑ i : Fin 4, (p i).1) * h4 d p b
def signedH3 (d : ℕ) (p : Part3 d) (b : Poly) : Poly :=
  (-1 : Poly) ^ (∑ i : Fin 3, (p i).1) * h3 d p b
def signedH2 (d : ℕ) (p : Part2 d) (b : Poly) : Poly :=
  (-1 : Poly) ^ (∑ i : Fin 2, (p i).1) * h2 d p b

def alphaEquation (d : ℕ) (b : Poly) (alpha : Poly4 d) : Prop :=
  ∀ p : Part4 d, fourAdmissible d p →
    (∑ q : Part4 d, W4 d p q * alpha q) = signedH4 d p b
def tripleEquation (d : ℕ) (b : Poly) (gamma : Poly3 d) : Prop :=
  ∀ p : Part3 d, threeAdmissible d p →
    (∑ q : Part3 d, W3 d p q * gamma q) = signedH3 d p b
def pairEquation (d : ℕ) (b : Poly) (theta : Poly2 d) : Prop :=
  ∀ p : Part2 d, twoAdmissible d p →
    (∑ q : Part2 d, W2 d p q * theta q) = signedH2 d p b

def alphaAt (alpha : Poly4 d) (p : Part4 d) : Poly := alpha p
def gammaAt (gamma : Poly3 d) (p : Part3 d) : Poly := gamma p
def thetaAt (theta : Poly2 d) (p : Part2 d) : Poly := theta p

def fourWord (d n m l r : ℕ) : List Bool :=
  List.replicate (d - 3) true ++ List.replicate r false ++ [true] ++
    List.replicate (l - r) false ++ [true] ++ List.replicate (m - l) false ++ [true] ++
    List.replicate (n - m) false ++ [true] ++ List.replicate (d - n + 1) false
def threeWord (d m l r : ℕ) : List Bool :=
  List.replicate (d - 2) true ++ List.replicate r false ++ [true] ++
    List.replicate (l - r) false ++ [true] ++ List.replicate (m - l) false ++ [true] ++
    List.replicate (d - m + 1) false

def native11Matrix (d n m : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := !![
  (Nat.choose (d - 3) 1 : ℚ), (Nat.choose (d - 2) 0 : ℚ), 0, 0;
  (Nat.choose (d - 3) 2 : ℚ), (Nat.choose (d - 2) 1 : ℚ), (Nat.choose (d - 1) 0 : ℚ), 0;
  (Nat.choose (d - 3) (m + 2) : ℚ), (Nat.choose (d - 2) (m + 1) : ℚ), (Nat.choose (d - 1) m : ℚ), (Nat.choose d (m - 1) : ℚ);
  (Nat.choose (d - 3) (n + 3) : ℚ), (Nat.choose (d - 2) (n + 2) : ℚ), (Nat.choose (d - 1) (n + 1) : ℚ), (Nat.choose d n : ℚ)]
def native21Matrix (d n m : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := !![
  (Nat.choose (d - 3) 1 : ℚ), (Nat.choose (d - 2) 0 : ℚ), 0, 0;
  (Nat.choose (d - 3) 3 : ℚ), (Nat.choose (d - 2) 2 : ℚ), (Nat.choose (d - 1) 1 : ℚ), (Nat.choose d 0 : ℚ);
  (Nat.choose (d - 3) (m + 2) : ℚ), (Nat.choose (d - 2) (m + 1) : ℚ), (Nat.choose (d - 1) m : ℚ), (Nat.choose d (m - 1) : ℚ);
  (Nat.choose (d - 3) (n + 3) : ℚ), (Nat.choose (d - 2) (n + 2) : ℚ), (Nat.choose (d - 1) (n + 1) : ℚ), (Nat.choose d n : ℚ)]
def Z11 (d n m : ℕ) (p : Part4 d) : Frac :=
  algebraMap Poly Frac (delta11 d n m * h4 d p Polynomial.X) /
    algebraMap Poly Frac (principalProduct d)
def Z21 (d n m : ℕ) (p : Part4 d) : Frac :=
  algebraMap Poly Frac (delta21 d n m * h4 d p Polynomial.X) /
    algebraMap Poly Frac (principalProduct d)

def tailR (d L j : ℕ) : ℕ := d - L + 1 + j
def tailS (d L : ℕ) (i : Fin L) (p : Fin L → ℕ) : ℕ :=
  d - L + i.1 + 1 + p ⟨L - 1 - i.1, by omega⟩
def tailEntry (d L : ℕ) (i j : Fin L) (p : Fin L → ℕ) : Frac := by
  classical
  exact if tailS d L i p < tailR d L j.1 then 0 else
    algebraMap ℚ Frac (Nat.choose (tailR d L j.1) (tailS d L i p - tailR d L j.1) : ℚ) /
      algebraMap Poly Frac (poch (2 * Polynomial.X + qconst (1 + tailR d L j.1 : ℚ)) (tailS d L i p - tailR d L j.1))
def coeffPolynomial (d : ℕ) : Poly :=
  Finset.sum (Finset.range 9) (fun k =>
    qconst (match k with
      | 0 => ((d+2:ℚ)*(d+3)/720)*(903*d^6+1123*d^5-7773*d^4+5581*d^3+13290*d^2+15436*d+10320)
      | 1 => (999*d^7+5144*d^6+2217*d^5-20095*d^4-12624*d^3+29441*d^2+28758*d+16920)/45
      | 2 => (3082*d^6+13218*d^5+4375*d^4-37392*d^3-22649*d^2+17766*d+5544)/18
      | 3 => 4/3*(566*d^5+2004*d^4+479*d^3-3603*d^2-1498*d+420)
      | 4 => 2*(1043*d^4+2958*d^3+441*d^2-2786*d-496)
      | 5 => 32*(116*d^3+248*d^2+17*d-81)
      | 6 => 64*(65*d^2+93*d+1)
      | 7 => 384*(7*d+5)
      | _ => 768) * Polynomial.X^k)

def tailPart (d L : ℕ) (p : Fin L → ℕ) : Fin d → ℕ := fun i =>
  if h : i.1 < L then i.1 + p ⟨L - 1 - i.1, by omega⟩ else i.1

def oneFactorDeletion (K : Type*) [Field K] {ι : Type*} [DecidableEq ι]
    (x : ι → K) (a : ι) (I : Finset ι) : K :=
  if a ∈ I then 0 else Finset.prod I (fun i => x i - x a)
def spanInf (u : ℝ → ℝ) (R : ℝ) : ℝ := sInf (u '' Set.Icc (-R/2) (R/2))

def alphaClaim (d : ℕ) (b : Poly) (alpha : Poly4 d) : Prop := alphaEquation d b alpha

def gammaClaim (d : ℕ) (b : Poly) (gamma : Poly3 d) : Prop := tripleEquation d b gamma

def thetaClaim (d : ℕ) (b : Poly) (theta : Poly2 d) : Prop := pairEquation d b theta

end
end MathlibPlus.Open.NewResearch2
