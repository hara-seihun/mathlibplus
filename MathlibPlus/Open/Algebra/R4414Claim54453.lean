import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.R4414Claim54453

noncomputable section
open Classical

/-- Coefficient variables for `x₂,…,x_m`, `y`, and `z₁,…,z_m`.
The polynomial variable is the separate `x₁` variable. -/
abbrev CoeffVar (m : ℕ) := Fin (m - 1) ⊕ (Unit ⊕ Fin m)
abbrev CoeffRing (m : ℕ) := MvPolynomial (CoeffVar m) ℤ
abbrev State (m : ℕ) := Fin (m + 1)

/-- The coefficient-ring variable `x_(j+2)`. -/
def xTailVar (m : ℕ) (j : Fin (m - 1)) : CoeffVar m :=
  Sum.inl j

/-- The coefficient-ring variable `y`. -/
def yVar (m : ℕ) : CoeffVar m :=
  Sum.inr (Sum.inl Unit.unit)

/-- The coefficient-ring variable `z_i`, where `i : Fin m` represents `z_(i+1)`. -/
def zVar (m : ℕ) (i : Fin m) : CoeffVar m :=
  Sum.inr (Sum.inr i)

/-- The nonzero state index corresponding to a state `1,…,m`. -/
def positiveStateIndex (m : ℕ) (s : State m) : Option (Fin m) :=
  Fin.cases none (fun i => some i) s

/-- The tail variable index for a positive nonzero state index. -/
def tailIndex {m : ℕ} (i : Fin m) (h : 0 < i.val) : Fin (m - 1) :=
  ⟨i.val - 1, by omega⟩

/-- Vertex weights `w₀=1`, `w₁=x₁`, and `w_(i+1)=x_(i+1)`. -/
def stateWeight (m : ℕ) (s : State m) : Polynomial (CoeffRing m) :=
  Fin.cases (Polynomial.C 1)
    (fun i =>
      if hi : i.val = 0 then Polynomial.X
      else Polynomial.C
        (MvPolynomial.X (xTailVar m (tailIndex i (by omega))))) s

/-- The Liu--Tang interaction matrix, with `q₀₀=1`, `qᵢᵢ=zᵢ`, and all
off-diagonal entries equal to `y`. -/
def stateInteraction (m : ℕ) (s t : State m) : Polynomial (CoeffRing m) :=
  if s = 0 ∧ t = 0 then
    Polynomial.C 1
  else if s = t then
    match positiveStateIndex m s with
    | none => Polynomial.C 1
    | some i => Polynomial.C (MvPolynomial.X (zVar m i))
  else
    Polynomial.C (MvPolynomial.X (yVar m))

/-- The interaction attached to an unordered graph edge. -/
def edgeInteraction {V : Type*} (m : ℕ) (σ : V → State m)
    (e : Sym2 V) : Polynomial (CoeffRing m) :=
  Sym2.lift
    ⟨(fun u v => stateInteraction m (σ u) (σ v)), by
      intro u v
      change stateInteraction m (σ u) (σ v) =
        stateInteraction m (σ v) (σ u)
      by_cases h : σ u = σ v
      · rw [h]
      · have h' : ¬σ v = σ u := fun h' => h h'.symm
        simp [stateInteraction, h, h', and_comm, eq_comm]⟩ e

/-- The root-conditioned message `M_s(T,r)`. -/
noncomputable def rootedMessage {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (T : SimpleGraph V) (r : V) (s : State m) :
    Polynomial (CoeffRing m) :=
  ∑ σ : V → State m,
    if σ r = s then
      (∏ v : V, stateWeight m (σ v)) *
        ∏ e ∈ T.edgeFinset, edgeInteraction m σ e
    else 0

/-- The pinned-parent factor `Φ_s(T,r)=Σ_t q_(s,t) M_t(T,r)`. -/
noncomputable def pinnedParentFactor {V : Type*} [Fintype V]
    [DecidableEq V] (m : ℕ) (T : SimpleGraph V) (r : V) (s : State m) :
    Polynomial (CoeffRing m) :=
  ∑ t : State m,
    stateInteraction m s t * rootedMessage m T r t

/-- The state-zero pinned factor, viewed as a polynomial in `x₁`. -/
noncomputable def stateZeroPinnedFactor {V : Type*} [Fintype V]
    [DecidableEq V] (m : ℕ) (T : SimpleGraph V) (r : V) :
    Polynomial (CoeffRing m) :=
  pinnedParentFactor m T r 0

/-- The reciprocal of a polynomial of degree `n`, written with the original
coefficients in reverse order. -/
noncomputable def reciprocalPolynomial {R : Type*} [Semiring R]
    (P : Polynomial R) : Polynomial R :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    Polynomial.C (P.coeff k) * Polynomial.X ^ (P.natDegree - k)

/-- Eisenstein's coefficient certificate at a prime element. -/
def eisensteinAt {R : Type*} [CommRing R]
    (p : R) (P : Polynomial R) : Prop :=
  Prime p ∧
    ¬p ∣ P.coeff P.natDegree ∧
    (∀ k : ℕ, k < P.natDegree → p ∣ P.coeff k) ∧
    ¬p ^ 2 ∣ P.coeff 0

/-- The coefficient of the full constant monomial in a polynomial in `x₁`
and the coefficient variables. -/
def fullConstantCoefficient {m : ℕ}
    (P : Polynomial (CoeffRing m)) : ℤ :=
  MvPolynomial.coeff 0 (P.coeff 0)

/-- Divisibility and congruence of the intermediate `x₁` coefficients. -/
def intermediateYDivisibility {m : ℕ}
    (P : Polynomial (CoeffRing m)) (n : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → k < n →
    MvPolynomial.X (yVar m) ∣ P.coeff k

/-- Claim 54453: the exact state-zero pinned-factor coefficient certificate,
reciprocal Eisenstein conclusion, irreducibility, and associate rigidity. -/
def claim54453 : Prop :=
  ∀ (m : ℕ), (hm : 1 ≤ m) →
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (T : SimpleGraph V) (r : V),
      T.IsTree →
      let P := stateZeroPinnedFactor m T r
      let n := Fintype.card V
      P.natDegree = n ∧
        intermediateYDivisibility P n ∧
        P.coeff n =
          MvPolynomial.X (yVar m) *
            MvPolynomial.X (zVar m ⟨0, by omega⟩) ^ (n - 1) ∧
        (∃ q : CoeffRing m,
          P.coeff 0 =
            (1 : CoeffRing m) + MvPolynomial.X (yVar m) * q) ∧
        ¬MvPolynomial.X (yVar m) ∣ P.coeff 0 ∧
        fullConstantCoefficient P = 1 ∧
        eisensteinAt (MvPolynomial.X (yVar m)) (reciprocalPolynomial P) ∧
        Irreducible P ∧
        (∀ {W : Type*} [Fintype W] [DecidableEq W]
          (U : SimpleGraph W) (q : W),
          U.IsTree →
          Associated P (stateZeroPinnedFactor m U q) →
          P = stateZeroPinnedFactor m U q)

end

end MathlibPlus.Open.Algebra.R4414Claim54453
