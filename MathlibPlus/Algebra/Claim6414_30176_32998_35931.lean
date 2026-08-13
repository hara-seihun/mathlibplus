import Mathlib

namespace MathlibPlus.Algebra

/-- The vertex weights in claim 6414, with the source's zero colour written
as the zero branch of `Fin.cases` and the remaining colours indexed by
`Fin m`.  The explicit hypothesis records `m ≥ 1`; it is not used to add
any further condition to the definition. -/
def finiteColourVertexWeight_claim6414 {R : Type*} [CommRing R]
    {m : ℕ} (_hm : 1 ≤ m) (x : Fin m → R) : Fin (m + 1) → R :=
  Fin.cases 1 (fun i => x i)

/-- The diagonal/off-diagonal edge-weight rule from claim 6414. -/
def finiteColourEdgeWeight_claim6414 {R : Type*} [CommRing R]
    {m : ℕ} (_hm : 1 ≤ m) (z : Fin (m + 1) → R) (_hz : z 0 = 1)
    (y : R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  fun s t => if s = t then z s else y

/-- The finite-colour component weight
`ρ_k^(m) = Σ_(s=0)^m w_s^k (z_s-y)^(k-1)` from claim 6414. -/
def finiteColourComponentWeight_claim6414 {R : Type*} [CommRing R]
    {m : ℕ} (hm : 1 ≤ m) (x : Fin m → R)
    (z : Fin (m + 1) → R) (_hz : z 0 = 1) (y : R) (k : ℕ) : R :=
  ∑ s : Fin (m + 1),
    (finiteColourVertexWeight_claim6414 hm x s) ^ k * (z s - y) ^ (k - 1)

end MathlibPlus.Algebra

namespace MathlibPlus.Combinatorics

/-- The complement-forest sum in claim 30176.  `evalAtMarkerZero` is the
source operation `(-)|_{c_J=0}`; keeping it as an explicit carrier avoids
inventing a multivariate forest-series representation. -/
def halfOrderComplementForestSum_claim30176
    {V R : Type*} [DecidableEq V] [CommRing R]
    (X : Finset V) (m J : ℕ) (_hm : m = 2 * J) (_hX : X.card = m)
    (connected : Finset V → Prop) [DecidablePred connected]
    (H : Finset V → Polynomial R)
    (evalAtMarkerZero : Polynomial R → ℕ → R) : R :=
  (X.powerset.filter (fun A => A.card = J ∧ connected A)).sum
    (fun A => evalAtMarkerZero (H (X \ A)) J)

end MathlibPlus.Combinatorics

namespace MathlibPlus.Analysis

/-- The six entries of the normalized internal derivative jet in claim 32998.
The derivative values are explicit arguments: the source's alternating
polynomial module supplies their relations, which are not silently replaced
by unrelated analytic assumptions here. -/
def normalizedInternalDerivativeJet_claim32998 {R : Type*} [DivisionRing R]
    (x H dHdx dHdy dHdxdy dHdy2 dHdx3 : R) : Fin 6 → R :=
  ![H / x, dHdx, 3 * dHdy / x, 3 * dHdxdy, -9 * dHdy2, 4 * dHdx3]

end MathlibPlus.Analysis

namespace MathlibPlus.LinearAlgebra

/-- The `i`th standard binary vector used in the condition `F_i(e_i)=0`. -/
def binaryBasisVector_claim35931 (n : ℕ) (i : Fin n) : Fin n → ZMod 2 :=
  fun j => if j = i then 1 else 0

/-- The indicator-composition `1_{S_i} ∘ F_i` from claim 35931. -/
noncomputable def quotientIndicator_claim35931 {n : ℕ} (d : Fin n → ℕ)
    (F : ∀ i : Fin n,
      (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2))
    (S : ∀ i : Fin n, Set (Fin (d i) → ZMod 2))
    (i : Fin n) : (Fin n → ZMod 2) → ZMod 2 := by
  classical
  exact fun v => if F i v ∈ S i then 1 else 0

/-- The dual carrier `A_i = im(F_i^*) + <ε_i>` in claim 35931.  The
submodule sum is the underlying subspace version of the displayed `⊕`;
the separate directness predicate below retains the notation's disjointness
condition. -/
def quotientDualCarrier_claim35931 {n : ℕ} (d : Fin n → ℕ)
    (F : ∀ i : Fin n,
      (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2))
    (i : Fin n) :
    Submodule (ZMod 2) ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :=
  Submodule.map (F i).dualMap ⊤ ⊔
    Submodule.span (ZMod 2) {LinearMap.proj i}

/-- The direct-sum condition in the displayed `⊕` of claim 35931. -/
def quotientDualCarrierDirect_claim35931 {n : ℕ} (d : Fin n → ℕ)
    (F : ∀ i : Fin n,
      (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2))
    (i : Fin n) : Prop :=
  Disjoint
    (Submodule.map (F i).dualMap ⊤)
    (Submodule.span (ZMod 2) {LinearMap.proj i})

/-- Lossless independent quotient representations for all selected
approximants in claim 35931.  The existential witnesses are per-index;
there is deliberately no compatibility conjunct between different indices. -/
def quotientApproximantRepresentation_claim35931 {n : ℕ}
    (g : ∀ i : Fin n, (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∃ d : Fin n → ℕ,
    ∃ F : ∀ i : Fin n,
      (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2),
    ∃ S : ∀ i : Fin n, Set (Fin (d i) → ZMod 2),
      ∀ i : Fin n,
        Function.Surjective (F i) ∧
          F i (binaryBasisVector_claim35931 n i) = 0 ∧
          ∀ v, g i v = quotientIndicator_claim35931 d F S i v

end MathlibPlus.LinearAlgebra
