import Mathlib

namespace MathlibPlus.Open

inductive GeneralizedDegreeVariable (m : ℕ) where
  | x (i : Fin (m + 1))
  | z (i : Fin (m + 1))
  | q (i j : Fin (m + 1))
  deriving DecidableEq

namespace GeneralizedDegreeVariable

variable {m : ℕ}

def qVariable (i j : Fin (m + 1)) : GeneralizedDegreeVariable m :=
  .q (min i j) (max i j)

end GeneralizedDegreeVariable

open GeneralizedDegreeVariable

noncomputable def generalizedDegreeEdgeWeight {m : ℕ}
    (i j : Fin (m + 1)) : MvPolynomial (GeneralizedDegreeVariable m) ℕ :=
  if i = j then
    MvPolynomial.X (.z i)
  else
    MvPolynomial.X (qVariable i j)

noncomputable def generalizedDegreeEdgeWeightOnSym2 {V : Type*} {m : ℕ}
    (τ : V → Fin (m + 1)) : Sym2 V → MvPolynomial (GeneralizedDegreeVariable m) ℕ :=
  Sym2.lift
    ⟨(fun u v => generalizedDegreeEdgeWeight (τ u) (τ v)), by
      intro u v
      unfold generalizedDegreeEdgeWeight
      by_cases h : τ u = τ v
      · simp [h]
      · have h' : τ v ≠ τ u := by
          intro huv
          exact h huv.symm
        simp [h, h', qVariable, min_comm, max_comm]⟩

noncomputable def generalizedDegreeInvariant {V : Type*} [Fintype V]
    (T : SimpleGraph V) (m : ℕ) :
    MvPolynomial (GeneralizedDegreeVariable m) ℕ := by
  letI : Fintype (V → Fin (m + 1)) := Fintype.ofFinite _
  letI : Fintype (T.edgeSet) := Fintype.ofFinite _
  exact Finset.univ.sum fun τ : V → Fin (m + 1) =>
    (Finset.univ.prod fun i : Fin (m + 1) =>
      MvPolynomial.X (.x i) ^ Fintype.card {v : V // τ v = i}) *
      T.edgeFinset.prod (fun e => generalizedDegreeEdgeWeightOnSym2 τ e)

def colorZero (m : ℕ) : Fin (m + 1) :=
  ⟨0, by omega⟩

def colorOne (m : ℕ) (hm : 2 ≤ m) : Fin (m + 1) :=
  ⟨1, by omega⟩

def colorTwo (m : ℕ) (hm : 2 ≤ m) : Fin (m + 1) :=
  ⟨2, by omega⟩

noncomputable def neighborSubsetDegreeSumProfile {V : Type*} [Fintype V]
    (T : SimpleGraph V) (t b s : ℕ) : ℕ := by
  classical
  exact Fintype.card {p : V × Finset V //
    p.2.card = t ∧
      p.2 ⊆ T.neighborFinset p.1 ∧
      T.degree p.1 = b ∧
      p.2.sum (fun u => T.degree u) = s}

def admissibleProfileParameters (n t b s : ℕ) : Prop :=
  1 ≤ t ∧
    t ≤ n - 1 ∧
    b ≥ t ∧
    s ≥ t ∧
    (0 : ℤ) ≤ (n : ℤ) + (t : ℤ) - 1 - (b : ℤ) - (s : ℤ)

noncomputable def targetProfileExponent (m n t b s : ℕ) (hm : 2 ≤ m) :
    GeneralizedDegreeVariable m →₀ ℕ :=
  Finsupp.single (.x (colorZero m)) (n - t - 1) +
    Finsupp.single (.x (colorOne m hm)) t +
    Finsupp.single (.x (colorTwo m hm)) 1 +
    Finsupp.single (qVariable (colorOne m hm) (colorTwo m hm)) t +
    Finsupp.single (qVariable (colorZero m) (colorOne m hm)) (s - t) +
    Finsupp.single (qVariable (colorZero m) (colorTwo m hm)) (b - t) +
    Finsupp.single (.z (colorZero m)) (n + t - 1 - b - s)

def claim_59988 : Prop :=
  ∀ (m n : ℕ),
    (hm : 2 ≤ m) →
    2 ≤ n →
    (∀ {V : Type*} [Fintype V] (T : SimpleGraph V),
      T.IsTree →
      Fintype.card V = n →
      ∀ t b s : ℕ,
        admissibleProfileParameters n t b s →
        neighborSubsetDegreeSumProfile T t b s =
          MvPolynomial.coeff
            (targetProfileExponent m n t b s hm)
            (generalizedDegreeInvariant T m)) ∧
    (∀ {V W : Type*} [Fintype V] [Fintype W]
      (T : SimpleGraph V) (U : SimpleGraph W),
      T.IsTree →
      U.IsTree →
      Fintype.card V = n →
      Fintype.card W = n →
      generalizedDegreeInvariant T m = generalizedDegreeInvariant U m →
      ∀ t b s : ℕ,
        admissibleProfileParameters n t b s →
        neighborSubsetDegreeSumProfile T t b s =
          neighborSubsetDegreeSumProfile U t b s) ∧
    (∀ {V W : Type*} [Fintype V] [Fintype W]
      (T : SimpleGraph V) (U : SimpleGraph W),
      T.IsTree →
      U.IsTree →
      Fintype.card V = n →
      Fintype.card W = n →
      (∃ t b s : ℕ,
        admissibleProfileParameters n t b s ∧
        3 ≤ t ∧
        neighborSubsetDegreeSumProfile T t b s ≠
          neighborSubsetDegreeSumProfile U t b s) →
      generalizedDegreeInvariant T m ≠ generalizedDegreeInvariant U m)

end MathlibPlus.Open
