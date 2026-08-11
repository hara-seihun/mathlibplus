import Mathlib

namespace MathlibPlus.MomentGeometry

noncomputable section

/-- A moment vector through degree three. -/
abbrev Moment4 := Fin 4 → ℝ

/-- The packet's factorial scaling `h_j = m_j / (2j)!`. -/
def factorialScaledMoment (m : Moment4) (j : Fin 4) : ℝ :=
  m j / Nat.factorial (2 * j.1)

/-- The scale-free ratio `R = m₁² / (m₀m₂)`. -/
def momentRatioR (m : Moment4) : ℝ :=
  m 1 ^ 2 / (m 0 * m 2)

/-- The scale-free ratio `S = m₁m₃ / m₂²`. -/
def momentRatioS (m : Moment4) : ℝ :=
  m 1 * m 3 / m 2 ^ 2

/-- Multiplying mass by `c` and support by `λ` leaves both packet ratios unchanged.
The positivity assumptions match the positive rescalings in C-0011 Record 1. -/
theorem momentRatioScaleInvariance
    (m₀ m₁ m₂ m₃ c scale : ℝ) (hc : 0 < c) (hscale : 0 < scale)
    (h₀₂ : m₀ * m₂ ≠ 0) (h₂ : m₂ ≠ 0) :
    (c * scale * m₁) ^ 2 / ((c * m₀) * (c * scale ^ 2 * m₂)) =
        m₁ ^ 2 / (m₀ * m₂) ∧
      (c * scale * m₁) * (c * scale ^ 3 * m₃) / (c * scale ^ 2 * m₂) ^ 2 =
        m₁ * m₃ / m₂ ^ 2 := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hscale0 : scale ≠ 0 := ne_of_gt hscale
  have h₀ : m₀ ≠ 0 := by
    intro hm₀
    apply h₀₂
    simp [hm₀]
  constructor
  · field_simp [hc0, hscale0, h₀, h₂]
  · field_simp [hc0, hscale0, h₀, h₂]

/-- In the Stieltjes region `R > 0`, `S ≥ 1`, either one-sided threshold from
C-0011 Record 5 places `(R,S)` in the exact open affine chamber. -/
theorem rankTwoOneSidedSufficientBounds
    (R S : ℝ) (hR : 0 < R) (hS : 1 ≤ S) :
    (7 / 15 < R ∨ 10 / 3 < S) → 10 / 3 < S + 5 * R := by
  rintro (hR' | hS')
  · nlinarith
  · nlinarith

/-- The finite Hankel feasibility domain from C-0011 Record 12. -/
def onePencilDomain (x : ℝ → ℝ) (r : ℝ → ℕ → ℝ) (N : ℕ) : Set ℝ :=
  {c | 0 < x c ∧ Matrix.PosSemidef (fun i j : Fin N => r c (i.1 + j.1))}

/-- Feasibility is nested under leading compression.  This is the nestedness clause
of C-0011 Record 12; no unformalized congruence, convexity, or closedness claim is
included. -/
theorem onePencilDomainsNested (x : ℝ → ℝ) (r : ℝ → ℕ → ℝ) :
    ∀ N, onePencilDomain x r (N + 1) ⊆ onePencilDomain x r N := by
  intro N c hc
  change 0 < x c ∧ Matrix.PosSemidef (fun i j : Fin (N + 1) => r c (i.1 + j.1)) at hc
  change 0 < x c ∧ Matrix.PosSemidef (fun i j : Fin N => r c (i.1 + j.1))
  refine ⟨hc.1, ?_⟩
  let e : Fin N → Fin (N + 1) := fun i => i.castSucc
  have hsub := hc.2.submatrix e
  have heq :
      ((fun i j : Fin N => r c (i.1 + j.1)) : Matrix (Fin N) (Fin N) ℝ) =
        Matrix.submatrix
          ((fun i j : Fin (N + 1) => r c (i.1 + j.1)) :
            Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) e e := by
    ext i j
    rfl
  rw [heq]
  exact hsub

/-- The compact nested-intersection mechanism isolated in C-0011 Record 13. -/
theorem nestedCompactCommonPoint (D : ℕ → Set ℝ)
    (hcompact : IsCompact (D 3))
    (hclosed : ∀ N, 3 ≤ N → IsClosed (D N) ∧ D N ⊆ D 3)
    (hnested : ∀ N, D (N + 1) ⊆ D N)
    (hnonempty : ∀ N, 3 ≤ N → (D N).Nonempty) :
    ∃ c, ∀ N, 3 ≤ N → c ∈ D N := by
  let E : ℕ → Set ℝ := fun n => D (n + 3)
  have hE_nested : ∀ n, E (n + 1) ⊆ E n := by
    intro n
    simpa [E, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnested (n + 3)
  have hE_nonempty : ∀ n, (E n).Nonempty := by
    intro n
    exact hnonempty (n + 3) (by omega)
  have hE_closed : ∀ n, IsClosed (E n) := by
    intro n
    exact (hclosed (n + 3) (by omega)).1
  have hE_compact : IsCompact (E 0) := by
    simpa [E] using hcompact
  obtain ⟨c, hc⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      E hE_nested hE_nonempty hE_compact hE_closed
  refine ⟨c, ?_⟩
  intro N hN
  have hindex : (N - 3) + 3 = N := by omega
  have hc' : c ∈ E (N - 3) := Set.mem_iInter.mp hc (N - 3)
  simpa [E, hindex] using hc'

end

end MathlibPlus.MomentGeometry
