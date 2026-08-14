import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim5457

/-- The degree of a vertex in the path on `k` vertices. -/
noncomputable def pathDegree (k : ℕ) (v : Fin k) : ℕ := by
  classical
  exact (Finset.filter (fun w : Fin k => (SimpleGraph.pathGraph k).Adj v w) Finset.univ).card

/-- The four path moments occurring in the admitted statement. -/
def constantMoment (k : ℕ) : Fin k → ℚ := fun _ => 1

noncomputable def degreeMoment (k : ℕ) : Fin k → ℚ :=
  fun v => pathDegree k v

noncomputable def secondDegreeMoment (k : ℕ) : Fin k → ℚ :=
  fun v => Nat.choose (pathDegree k v) 2

noncomputable def secondJetMoment (k : ℕ) : Fin k → ℚ := by
  classical
  exact fun v =>
    (Finset.filter (fun w : Fin k => (SimpleGraph.pathGraph k).Adj v w) Finset.univ).sum
      (fun w => (pathDegree k w - 1 : ℚ))

/-- Functions on rooted vertices fixed by every path automorphism.  For a path,
    the nontrivial automorphism is reversal. -/
def pathOrbitSpace (k : ℕ) : Submodule ℚ (Fin k → ℚ) where
  carrier := {f | ∀ v : Fin k, f (Fin.rev v) = f v}
  zero_mem' := by
    intro v
    simp
  add_mem' := by
    intro f g hf hg v
    simp [hf v, hg v]
  smul_mem' := by
    intro a f hf v
    simp [hf v]

/-- The span of the four moments before restricting to the path orbit space. -/
noncomputable def pathMomentSpan (k : ℕ) : Submodule ℚ (Fin k → ℚ) :=
  Submodule.span ℚ {
    constantMoment k,
    degreeMoment k,
    secondDegreeMoment k,
    secondJetMoment k
  }

/-- `W(P_k)` inside the path-automorphism orbit space. -/
noncomputable def pathMomentSubspace (k : ℕ) : Submodule ℚ (pathOrbitSpace k) :=
  Submodule.comap (Submodule.subtype (pathOrbitSpace k)) (pathMomentSpan k)

/-- On paths, the admitted unrestricted contraction saturation is the full
    automorphism orbit space. -/
abbrev contractionSaturation (k : ℕ) : Submodule ℚ (Fin k → ℚ) :=
  pathOrbitSpace k

/-- The resulting `L_nat(P_k) = Sat_ctr(W)(P_k) / W(P_k)` quotient. -/
abbrev naturalLeakage (k : ℕ) :=
  (contractionSaturation k) ⧸ pathMomentSubspace k

def ceilHalf (k : ℕ) : ℕ := (k + 1) / 2

/-- Exact unbounded leakage dimension for paths, including unboundedness in `k`. -/
def naturalLeakageDimension_claim5457 : Prop :=
  (∀ k : ℕ, 7 ≤ k →
    Module.finrank ℚ (naturalLeakage k) = ceilHalf k - 3) ∧
  (∀ n : ℕ, ∃ k : ℕ,
    7 ≤ k ∧ n < Module.finrank ℚ (naturalLeakage k))

end MathlibPlus.Open.Combinatorics.Claim5457
