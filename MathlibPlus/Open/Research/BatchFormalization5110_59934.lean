import Mathlib

namespace MathlibPlus.Open.Research.BatchLinearGrowth

/-- The action of a word `i₁ ... iₘ` is `Gᵢₘ ⋯ Gᵢ₁`. -/
def wordApply {𝕜 : Type*} [DivisionRing 𝕜] {V : ℕ → Type*}
    [∀ n, AddCommGroup (V n)] [∀ n, Module 𝕜 (V n)]
    {k : ℕ} (G : Fin k → ∀ n, V n →ₗ[𝕜] V (n + 1)) :
    (n : ℕ) → V n → (w : List (Fin k)) → V (n + w.length)
  | n, v, [] => v
  | n, v, i :: w =>
      cast (by simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
        (wordApply G (n + 1) (G i n v) w)

/-- The span of all words of length `m` from the seed in degree `n₀ + m`. -/
def wordSpan {𝕜 : Type*} [DivisionRing 𝕜] {V : ℕ → Type*}
    [∀ n, AddCommGroup (V n)] [∀ n, Module 𝕜 (V n)]
    (n₀ m k : ℕ) (G : Fin k → ∀ n, V n →ₗ[𝕜] V (n + 1)) (e : V n₀) :
    Submodule 𝕜 (V (n₀ + m)) :=
  Submodule.span 𝕜 {v | ∃ w : Fin m → Fin k,
    v = cast (by simp) (wordApply G n₀ e (List.ofFn w))}

/-- A finite family of degree-one raising operators is a growth alphabet. -/
def IsGrowthAlphabet {𝕜 : Type*} [DivisionRing 𝕜] {V : ℕ → Type*}
    [∀ n, AddCommGroup (V n)] [∀ n, Module 𝕜 (V n)]
    (n₀ k : ℕ) (G : Fin k → ∀ n, V n →ₗ[𝕜] V (n + 1)) (e : V n₀) : Prop :=
  ∀ m : ℕ, wordSpan n₀ m k G e = ⊤

/-- The limsup entropy of a graded family with finite-dimensional pieces. -/
noncomputable def growthEntropy {𝕜 : Type*} [DivisionRing 𝕜] {V : ℕ → Type*}
    [∀ n, AddCommGroup (V n)] [∀ n, Module 𝕜 (V n)] (_n₀ : ℕ) : ℝ :=
  Filter.limsup
    (fun n : ℕ => Real.rpow (Module.finrank 𝕜 (V n) : ℝ) (1 / (n : ℝ))) Filter.atTop

/-- Entropy lower bound for finite growth alphabets. -/
def EntropyLowerBoundFiniteGrowthAlphabets : Prop :=
  ∀ (𝕜 : Type*) [DivisionRing 𝕜] (V : ℕ → Type*)
    [∀ n, AddCommGroup (V n)] [∀ n, Module 𝕜 (V n)]
    (n₀ k : ℕ) (e : V n₀)
    (G : Fin k → ∀ n, V n →ₗ[𝕜] V (n + 1)),
    (∀ n : ℕ, FiniteDimensional 𝕜 (V n)) →
    (∀ n ≥ n₀,
      Fintype.card (Fin (n - n₀) → Fin k) ≤ k ^ (n - n₀)) ∧
    (IsGrowthAlphabet n₀ k G e →
      (∀ n ≥ n₀, Module.finrank 𝕜 (V n) ≤ k ^ (n - n₀)) ∧
      growthEntropy (𝕜 := 𝕜) (V := V) n₀ ≤ (k : ℝ) ∧
      Nat.ceil (growthEntropy (𝕜 := 𝕜) (V := V) n₀) ≤ k)

end MathlibPlus.Open.Research.BatchLinearGrowth

namespace MathlibPlus.Open.Research.BatchTreeColoring

inductive ColorVar (m : ℕ) where
  | x (i : Fin (m + 1))
  | z (i : Fin (m + 1))
  | q (i j : Fin (m + 1))
deriving DecidableEq, Fintype

def qVariable {m : ℕ} (i j : Fin (m + 1)) : ColorVar m :=
  if i ≤ j then ColorVar.q i j else ColorVar.q j i

noncomputable def vertexWeight {m : ℕ} (i : Fin (m + 1)) : MvPolynomial (ColorVar m) ℕ :=
  MvPolynomial.X (ColorVar.x i)

noncomputable def edgeWeight {m : ℕ} (i j : Fin (m + 1)) : MvPolynomial (ColorVar m) ℕ :=
  if i = j then MvPolynomial.X (ColorVar.z i) else MvPolynomial.X (qVariable i j)

/-- The complete fixed-`m` generalized-degree coloring invariant. -/
noncomputable def fixedInvariant (m n : ℕ) (T : SimpleGraph (Fin n)) :
    MvPolynomial (ColorVar m) ℕ := by
  classical
  exact ∑ τ : Fin n → Fin (m + 1),
    (∏ v : Fin n, vertexWeight (τ v)) *
      (∏ u : Fin n,
        ∏ v : Fin n,
          if u < v ∧ T.Adj u v then edgeWeight (τ u) (τ v) else 1)

noncomputable def neighborsIn {n : ℕ} (T : SimpleGraph (Fin n)) (u : Fin n)
    (B : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact B.filter (fun v => T.Adj u v)

noncomputable def boundarySize {n : ℕ} (T : SimpleGraph (Fin n))
    (B : Finset (Fin n)) : ℕ := by
  classical
  exact ((Finset.univ.product Finset.univ).filter
    (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ T.Adj p.1 p.2 ∧
        ((p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.1 ∉ B ∧ p.2 ∈ B)))).card

/-- The connected-core two-boundary-vertex profile. -/
noncomputable def boundaryProfile (n k a b : ℕ) (T : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun p : Finset (Fin n) × (Fin n × Fin n) =>
      p.1.card = k ∧
      (T.induce (p.1 : Set (Fin n))).Connected ∧
      p.2.1 ∉ p.1 ∧ p.2.2 ∉ p.1 ∧ p.2.1 < p.2.2 ∧
      ¬ T.Adj p.2.1 p.2.2 ∧
      (neighborsIn T p.2.1 p.1).card = 1 ∧
      (neighborsIn T p.2.2 p.1).card = 1 ∧
      T.degree p.2.1 + T.degree p.2.2 = a ∧
      boundarySize T p.1 = b)).card

def c0 {m : ℕ} (_hm : 2 ≤ m) : Fin (m + 1) := ⟨0, by omega⟩
def c1 {m : ℕ} (_hm : 2 ≤ m) : Fin (m + 1) := ⟨1, by omega⟩
def c2 {m : ℕ} (_hm : 2 ≤ m) : Fin (m + 1) := ⟨2, by omega⟩

def intNat (z : ℤ) : ℕ := z.toNat

noncomputable def targetExponent (m n k a b : ℕ) (hm : 2 ≤ m) : ColorVar m →₀ ℕ :=
  Finsupp.single (ColorVar.x (c0 hm)) (intNat ((n : ℤ) - k - 2)) +
  Finsupp.single (ColorVar.x (c1 hm)) 2 +
  Finsupp.single (ColorVar.x (c2 hm)) k +
  Finsupp.single (ColorVar.z (c2 hm)) (k - 1) +
  Finsupp.single (qVariable (c1 hm) (c2 hm)) 2 +
  Finsupp.single (qVariable (c0 hm) (c1 hm)) (a - 2) +
  Finsupp.single (qVariable (c0 hm) (c2 hm)) (b - 2) +
  Finsupp.single (ColorVar.z (c0 hm))
    (intNat ((n : ℤ) - k - a - b + 2))

/-- The exact coefficient identity and its profile-obstruction consequences. -/
def FixedMInvariantTwoBoundaryProfile : Prop :=
  ∀ (m n : ℕ) (hm : 2 ≤ m) (hn : 3 ≤ n),
    (∀ T : SimpleGraph (Fin n), T.IsTree →
      (∀ k a b : ℕ, 1 ≤ k → 2 ≤ a → 2 ≤ b → k + 2 ≤ n →
        (0 : ℤ) ≤ (n : ℤ) - k - a - b + 2 →
        boundaryProfile n k a b T =
          MvPolynomial.coeff (targetExponent m n k a b hm)
            (fixedInvariant m n T))) ∧
    (∀ T₁ T₂ : SimpleGraph (Fin n), T₁.IsTree → T₂.IsTree →
      fixedInvariant m n T₁ = fixedInvariant m n T₂ →
      ∀ k a b : ℕ, 1 ≤ k → 2 ≤ a → 2 ≤ b → k + 2 ≤ n →
        (0 : ℤ) ≤ (n : ℤ) - k - a - b + 2 →
        boundaryProfile n k a b T₁ = boundaryProfile n k a b T₂) ∧
    (∀ T₁ T₂ : SimpleGraph (Fin n), T₁.IsTree → T₂.IsTree →
      ∀ k a b : ℕ, 1 ≤ k → 2 ≤ a → 2 ≤ b → k + 2 ≤ n →
        (0 : ℤ) ≤ (n : ℤ) - k - a - b + 2 →
        boundaryProfile n k a b T₁ ≠ boundaryProfile n k a b T₂ →
        fixedInvariant m n T₁ ≠ fixedInvariant m n T₂)

end MathlibPlus.Open.Research.BatchTreeColoring
