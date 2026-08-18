import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

namespace MathlibPlus.Open.ResearchFormalization.R1932Claim36292

open scoped BigOperators

noncomputable section

private def pathGraph1932 (m : ℕ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (fun i j => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)

private def castMvQRingHom1932 :
    MvPolynomial ℕ ℤ →+* MvPolynomial ℕ ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ)

private def castMvQ1932 (p : MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℚ :=
  castMvQRingHom1932 p

private def forestU1932 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℤ :=
  MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial G

private def forestUQ1932 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℚ :=
  castMvQ1932 (forestU1932 G)

private def induced1932 {V : Type} (G : SimpleGraph V)
    (S : Finset V) : SimpleGraph {v // v ∈ S} :=
  G.induce {v | v ∈ S}

private noncomputable def forestUOn1932 {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    MvPolynomial ℕ ℤ :=
  letI := Classical.decEq {v // v ∈ S}
  forestU1932 (induced1932 G S)

private noncomputable def forestUQOn1932 {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    MvPolynomial ℕ ℚ :=
  castMvQ1932 (forestUOn1932 G S)

private def restrictedAdj1932 {V : Type} (G : SimpleGraph V)
    (S : Finset V) (u v : V) : Prop :=
  u ∈ S ∧ v ∈ S ∧ G.Adj u v

private def restrictedReach1932 {V : Type} (G : SimpleGraph V)
    (S : Finset V) : V → V → Prop :=
  Relation.ReflTransGen (restrictedAdj1932 G S)

private noncomputable def restrictedComponent1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (v : V) : Finset V :=
  letI := Classical.propDecidable
  S.filter (restrictedReach1932 G S v)

private noncomputable def restrictedComponents1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    Finset (Finset V) :=
  letI := Classical.propDecidable
  letI := Classical.decEq (Finset V)
  S.image (restrictedComponent1932 G S)

private def connectedOn1932 {V : Type} (G : SimpleGraph V)
    (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, restrictedReach1932 G S u v

private def treeGraph1932 {V : Type} (G : SimpleGraph V) : Prop :=
  G.IsAcyclic ∧ ∀ u v, Relation.ReflTransGen G.Adj u v

private noncomputable def fringeSets1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    Finset (Finset V) :=
  restrictedComponents1932 G (Finset.univ.erase r)

private noncomputable def pruningPolynomialZ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    Polynomial (MvPolynomial ℕ ℤ) :=
  letI := Classical.propDecidable
  let S : Finset V := Finset.univ
  ∑ Q ∈ S.powerset,
    if r ∈ Q ∧ connectedOn1932 G Q then
      Polynomial.C (forestUOn1932 G (S \ Q)) *
        Polynomial.X ^ (Fintype.card V - Q.card)
    else 0

private noncomputable def pruningPolynomialQ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  letI := Classical.propDecidable
  let S : Finset V := Finset.univ
  ∑ Q ∈ S.powerset,
    if r ∈ Q ∧ connectedOn1932 G Q then
      Polynomial.C (forestUQOn1932 G (S \ Q)) *
        Polynomial.X ^ (Fintype.card V - Q.card)
    else 0

private noncomputable def childFactorZ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (r : V) (C : Finset V) :
    Polynomial (MvPolynomial ℕ ℤ) :=
  letI := Classical.decEq {v // v ∈ C}
  letI := Classical.propDecidable
  ∑ c ∈ C.attach,
    if G.Adj r c.1 then
      pruningPolynomialZ1932 (induced1932 G C) c
    else 0

private noncomputable def childFactorQ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (r : V) (C : Finset V) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  letI := Classical.decEq {v // v ∈ C}
  letI := Classical.propDecidable
  ∑ c ∈ C.attach,
    if G.Adj r c.1 then
      pruningPolynomialQ1932 (induced1932 G C) c
    else 0

private noncomputable def childProductZ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    Polynomial (MvPolynomial ℕ ℤ) :=
  letI := Classical.decEq (Finset V)
  ∏ C ∈ fringeSets1932 G r, childFactorZ1932 G Finset.univ r C

private noncomputable def childProductQ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  letI := Classical.decEq (Finset V)
  ∏ C ∈ fringeSets1932 G r, childFactorQ1932 G Finset.univ r C

private noncomputable def dPolynomialZ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    Polynomial (MvPolynomial ℕ ℤ) :=
  childProductZ1932 G r

private noncomputable def dPolynomialQ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  childProductQ1932 G r

private noncomputable def pruningRecursionZ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) : Prop :=
  pruningPolynomialZ1932 G r =
    Polynomial.X ^ Fintype.card V *
        Polynomial.C (forestU1932 G) + dPolynomialZ1932 G r

private noncomputable def pruningRecursionQ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) : Prop :=
  pruningPolynomialQ1932 G r =
    Polynomial.X ^ Fintype.card V *
        Polynomial.C (forestUQ1932 G) + dPolynomialQ1932 G r

private noncomputable def properFringeCount1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V)
    (j : ℕ) : ℕ :=
  ((fringeSets1932 G r).filter (fun C => C.card = j)).card

private noncomputable def uTwoZ1932 : MvPolynomial ℕ ℤ :=
  forestU1932 (pathGraph1932 2)

private noncomputable def uThreeZ1932 : MvPolynomial ℕ ℤ :=
  forestU1932 (pathGraph1932 3)

private noncomputable def uTwoQ1932 : MvPolynomial ℕ ℚ :=
  forestUQ1932 (pathGraph1932 2)

private noncomputable def uThreeQ1932 : MvPolynomial ℕ ℚ :=
  forestUQ1932 (pathGraph1932 3)

private def polynomialRemainder1932 {A : Type*} [Semiring A]
    (P : Polynomial A) (k : ℕ) : Prop :=
  ∀ j : ℕ, j < k → P.coeff j = 0

private abbrev SeriesQ1932 := ℕ → MvPolynomial ℕ ℚ

private def seriesZero1932 : SeriesQ1932 := fun _ => 0

private def seriesOne1932 : SeriesQ1932 := fun n =>
  if n = 0 then 1 else 0

private def seriesAdd1932 (f g : SeriesQ1932) : SeriesQ1932 :=
  fun n => f n + g n

private def seriesSub1932 (f g : SeriesQ1932) : SeriesQ1932 :=
  fun n => f n - g n

private def seriesMul1932 (f g : SeriesQ1932) : SeriesQ1932 :=
  fun n => ∑ k ∈ Finset.range (n + 1), f k * g (n - k)

private def seriesPow1932 : SeriesQ1932 → ℕ → SeriesQ1932
  | f, 0 => seriesOne1932
  | f, n + 1 => seriesMul1932 (seriesPow1932 f n) f

private def seriesOfPolynomial1932
    (P : Polynomial (MvPolynomial ℕ ℚ)) : SeriesQ1932 :=
  fun n => P.coeff n

private def seriesMonomial1932 (n : ℕ) (a : MvPolynomial ℕ ℚ) : SeriesQ1932 :=
  fun j => if j = n then a else 0

private def seriesRemainder1932 (f : SeriesQ1932) (k : ℕ) : Prop :=
  ∀ n : ℕ, n < k → f n = 0

private def seriesLog1932 (f : SeriesQ1932) : SeriesQ1932 :=
  fun n =>
    ∑ k ∈ Finset.range (n + 1),
      if k = 0 then 0 else
        ((((-1 : ℚ) ^ (k + 1)) / (k : ℚ)) : ℚ) •
          (seriesPow1932 f k n)

private def seriesInverse1932 (D : Polynomial (MvPolynomial ℕ ℚ))
    (inv : SeriesQ1932) : Prop :=
  seriesMul1932 (seriesOfPolynomial1932 D) inv = seriesOne1932

private def seriesOfPolynomialZ1932
    (P : Polynomial (MvPolynomial ℕ ℤ)) : ℕ → MvPolynomial ℕ ℤ :=
  fun n => P.coeff n

private def inverseMainPolynomialQ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  let ell := properFringeCount1932 G r 1
  let q₂ := properFringeCount1932 G r 2
  let q₃ := properFringeCount1932 G r 3
  let x₁ : MvPolynomial ℕ ℚ := MvPolynomial.X 1
  Polynomial.C 1 -
      Polynomial.C ((ell : ℚ) • x₁) * Polynomial.X +
    Polynomial.C
      (((Nat.choose (ell + 1) 2 : ℚ) • (x₁ ^ 2)) -
        (q₂ : ℚ) • uTwoQ1932) * Polynomial.X ^ 2 +
    Polynomial.C
      (-((Nat.choose (ell + 2) 3 : ℚ) • (x₁ ^ 3)) +
          ((q₂ : ℚ) * (ell + 1 : ℚ)) • x₁ * uTwoQ1932 -
          (q₃ : ℚ) • uThreeQ1932) * Polynomial.X ^ 3

private noncomputable def kappaMainPolynomialQ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    Polynomial (MvPolynomial ℕ ℚ) :=
  let m := Fintype.card V
  let ell := properFringeCount1932 G r 1
  let q₂ := properFringeCount1932 G r 2
  let q₃ := properFringeCount1932 G r 3
  let x₁ : MvPolynomial ℕ ℚ := MvPolynomial.X 1
  let u := forestUQ1932 G
  Polynomial.C u * Polynomial.X ^ m -
      Polynomial.C ((ell : ℚ) • x₁ * u) * Polynomial.X ^ (m + 1) +
    Polynomial.C
      (((Nat.choose (ell + 1) 2 : ℚ) • (x₁ ^ 2) -
          (q₂ : ℚ) • uTwoQ1932) * u) * Polynomial.X ^ (m + 2) +
    Polynomial.C
      ((-((Nat.choose (ell + 2) 3 : ℚ) • (x₁ ^ 3)) +
          ((q₂ : ℚ) * (ell + 1 : ℚ)) • x₁ * uTwoQ1932 -
          (q₃ : ℚ) • uThreeQ1932) * u) * Polynomial.X ^ (m + 3)

private def edgeDeletedAdj1932 {V : Type} (G : SimpleGraph V)
    (a b u v : V) : Prop :=
  G.Adj u v ∧ ¬ ((u = a ∧ v = b) ∨ (u = b ∧ v = a))

private def edgeDeletedReach1932 {V : Type} (G : SimpleGraph V)
    (a b : V) : V → V → Prop :=
  Relation.ReflTransGen (edgeDeletedAdj1932 G a b)

private noncomputable def sideSet1932 {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (a b : V) : Finset V :=
  letI := Classical.propDecidable
  Finset.univ.filter (edgeDeletedReach1932 G a b a)

private noncomputable def sideDPolynomialQ1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (r : V) : Polynomial (MvPolynomial ℕ ℚ) :=
  letI := Classical.decEq (Finset V)
  ∏ C ∈ restrictedComponents1932 G (S.erase r),
    childFactorQ1932 G S r C

private noncomputable def sideUQ1932 {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    MvPolynomial ℕ ℚ := forestUQOn1932 G S

private noncomputable def sideKappa1932 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (r : V) (inv : SeriesQ1932) : SeriesQ1932 :=
  seriesLog1932
    (seriesAdd1932 seriesOne1932
      (seriesMul1932
        (seriesMonomial1932 S.card (sideUQ1932 G S)) inv))

end

private noncomputable def betaOne36292 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    MvPolynomial ℕ ℤ :=
  forestUOn1932 G (Finset.univ.erase r)

private noncomputable def branchUPolynomials36292 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    Multiset (MvPolynomial ℕ ℤ) :=
  (fringeSets1932 G r).val.map (forestUOn1932 G)

private noncomputable def branchProduct36292 {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) :
    MvPolynomial ℕ ℤ :=
  (branchUPolynomials36292 G r).prod

private def lowerUInjective36292 (m : ℕ) : Prop :=
  ∀ {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (K : SimpleGraph W),
    Fintype.card V < m →
      Fintype.card W < m →
        treeGraph1932 G →
          treeGraph1932 K →
            forestU1932 G = forestU1932 K →
              Nonempty (G ≃g K)

private def rootedGraphIso36292 {V W : Type}
    (G : SimpleGraph V) (r : V) (K : SimpleGraph W) (s : W) : Prop :=
  ∃ e : V ≃ W,
    (∀ u v, G.Adj u v ↔ K.Adj (e u) (e v)) ∧ e r = s

def claim36292_multiplicativeHostCollarInverse : Prop :=
  (∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V),
    treeGraph1932 G →
      betaOne36292 G r = branchProduct36292 G r ∧
        (∀ C ∈ fringeSets1932 G r,
          Irreducible (forestUOn1932 G C))) ∧
    (∀ {V W : Type} [Fintype V] [DecidableEq V]
      [Fintype W] [DecidableEq W]
      (G : SimpleGraph V) (r : V) (K : SimpleGraph W) (s : W),
      treeGraph1932 G →
        treeGraph1932 K →
          betaOne36292 G r = betaOne36292 K s →
            branchUPolynomials36292 G r = branchUPolynomials36292 K s) ∧
    (∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (r s : V),
      treeGraph1932 G →
        lowerUInjective36292 (Fintype.card V) →
          betaOne36292 G r = betaOne36292 G s →
            rootedGraphIso36292 G r G s)

end MathlibPlus.Open.ResearchFormalization.R1932Claim36292
