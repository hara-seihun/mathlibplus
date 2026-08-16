import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.BatchO0295

noncomputable section

abbrev VertexSpace (N : ℕ) := Fin (N + 1) → ℝ
abbrev EdgeSpace (N : ℕ) := Fin N → ℝ

/-- The ordered free vertex basis `v₀, ..., v_N`. -/
def vertexBasis (N : ℕ) (k : Fin (N + 1)) : VertexSpace N :=
  Pi.single k 1

/-- The oriented edge basis `a₁, ..., a_N`, indexed by `Fin N`. -/
def edgeBasis (N : ℕ) (j : Fin N) : EdgeSpace N :=
  Pi.single j 1

/-- The event chain `E = sum e_j v_j`. -/
def eventChain {N : ℕ} (e : Fin (N + 1) → ℝ) : VertexSpace N :=
  ∑ k : Fin (N + 1), e k • vertexBasis N k

/-- The edge chain represented by coefficients in the oriented edge basis. -/
def edgeChain {N : ℕ} (h : EdgeSpace N) : EdgeSpace N :=
  ∑ j : Fin N, h j • edgeBasis N j

/-- The incidence boundary on the oriented edge basis. -/
def edgeBoundaryBasis (N : ℕ) (j : Fin N) : VertexSpace N :=
  vertexBasis N j.succ - vertexBasis N j.castSucc

/-- The boundary of an edge chain. -/
def edgeBoundary {N : ℕ} (h : EdgeSpace N) : VertexSpace N :=
  ∑ j : Fin N, h j • edgeBoundaryBasis N j

/-- The prefix charge `S_k(E) = sum_{j=0}^k e_j`. -/
def prefixCharge {N : ℕ} (e : Fin (N + 1) → ℝ)
    (k : Fin (N + 1)) : ℝ :=
  ∑ j ∈ Finset.Iic k, e j

/-- The finite edge `ell-infinity` and `ell-one` norms. -/
noncomputable def edgeInfinityNorm {N : ℕ} (h : EdgeSpace N) : ℝ :=
  sSup {r : ℝ | ∃ j : Fin N, r = |h j|}

def edgeOneNorm {N : ℕ} (h : EdgeSpace N) : ℝ :=
  ∑ j : Fin N, |h j|

/-- The canonical filling `H_E = -sum_{j=1}^N S_{j-1}(E) a_j`. -/
def canonicalFilling {N : ℕ}
    (e : Fin (N + 1) → ℝ) : EdgeSpace N :=
  fun j => -prefixCharge e j.castSucc

/-- A zero-mass event chain on the ordered finite free path.  The carrier,
oriented incidence equation, event-chain expression, and prefix-charge
expression are all part of this declaration, not detached helper facts. -/
def claim15220 (N : ℕ) (e : Fin (N + 1) → ℝ) : Prop :=
  (∑ j : Fin (N + 1), e j) = 0 ∧
    (∀ j : Fin N,
      edgeBoundary (edgeBasis N j) =
        vertexBasis N j.succ - vertexBasis N j.castSucc) ∧
      eventChain e =
        ∑ j : Fin (N + 1), e j • vertexBasis N j ∧
      (∀ k : Fin (N + 1),
        prefixCharge e k = ∑ j ∈ Finset.Iic k, e j)

/-- Every zero-mass path event chain has the unique filling satisfying the
incidence boundary equation.  Uniqueness is among all fillings satisfying
that equation; the canonical formula and both norm identities are stated
separately for every such filling. -/
def claim15221 : Prop :=
  ∀ (N : ℕ) (e : Fin (N + 1) → ℝ),
    claim15220 N e →
      (∃! H : EdgeSpace N,
        edgeBoundary H = eventChain e) ∧
        (∀ H : EdgeSpace N,
          edgeBoundary H = eventChain e →
            H = canonicalFilling e ∧
              H =
                ∑ j : Fin N,
                  (-prefixCharge e j.castSucc) • edgeBasis N j ∧
              edgeInfinityNorm H =
                sSup
                  {r : ℝ |
                    ∃ k : Fin N, r = |prefixCharge e k.castSucc|} ∧
              edgeOneNorm H =
                ∑ k : Fin N, |prefixCharge e k.castSucc|)

end

end MathlibPlus.Open.Research.BatchO0295
