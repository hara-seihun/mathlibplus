import Mathlib

namespace MathlibPlus.Open.Research

def claim13507 : Prop :=
  ∀ (x g t : ℝ),
    let θ : ℝ := t * Real.log 2
    let Id2 : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j => if i = j then 1 else 0
    let X : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j =>
        if i = 0 ∧ j = 1 then 1
        else if i = 1 ∧ j = 0 then 1
        else 0
    let Y : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j =>
        if i = 0 ∧ j = 1 then -Complex.I
        else if i = 1 ∧ j = 0 then Complex.I
        else 0
    let Z : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j => if i = j then if i = 0 then 1 else -1 else 0
    let mul2 : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2) (Fin 2) ℂ :=
      fun A B i j => ∑ k : Fin 2, A i k * B k j
    let adj2 : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ :=
      fun A i j => star (A j i)
    let Pθ : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j =>
        if i = 0 ∧ j = 0 then
          Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))
        else if i = 1 ∧ j = 1 then
          Complex.exp (-Complex.I * ((θ / 2 : ℝ) : ℂ))
        else 0
    let Cs : Matrix (Fin 2) (Fin 2) ℂ := mul2 (mul2 Pθ X) (adj2 Pθ)
    let tensor : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun A B (i, k) (j, l) => A i j * B k l
    let mul4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun A B i j => ∑ k : Fin 2 × Fin 2, A i k * B k j
    let Rh := tensor Cs Id2
    let Rc := tensor Id2 X
    let D := mul4 Rh Rc
    let J := tensor Z Y
    let Yθ := mul2 (mul2 Pθ Y) (adj2 Pθ)
    let N := tensor Yθ Z
    let I4 := tensor Id2 Id2
    let d : ℝ := 2 + x
    let ρ : ℝ := g / d
    let A_x : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      ((d / 4 : ℝ) : ℂ) • I4 - ((1 / 2 : ℝ) : ℂ) • D
    let Qvis : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      ((d / 4 : ℝ) : ℂ) • I4 - ((1 / 2 : ℝ) : ℂ) • D -
        ((g / 4 : ℝ) : ℂ) • J
    let Qstar : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      mul4 A_x (I4 - (ρ : ℂ) • J)
    let hermitian : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ → Prop :=
      fun Q => ∀ i j, Q i j = star (Q j i)
    let psd : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ → Prop :=
      fun Q =>
        hermitian Q ∧
          ∀ v : Fin 2 × Fin 2 → ℂ,
            0 ≤ (∑ i : Fin 2 × Fin 2, star (v i) * (Matrix.mulVec Q v) i).re
    (mul4 D J = N) ∧
      Qstar = mul4 A_x (I4 - (ρ : ℂ) • J) ∧
      (∃! c : ℝ, Qvis + (c : ℂ) • N = Qstar) ∧
      (Qstar = Qvis + ((g / (2 * d) : ℝ) : ℂ) • N) ∧
      (psd Qstar ↔ |g| ≤ d)

def claim13511 : Prop :=
  ∀ (a b c t d e f : ℝ),
    let Id2 : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j => if i = j then 1 else 0
    let X : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j =>
        if i = 0 ∧ j = 1 then 1
        else if i = 1 ∧ j = 0 then 1
        else 0
    let Y : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j =>
        if i = 0 ∧ j = 1 then -Complex.I
        else if i = 1 ∧ j = 0 then Complex.I
        else 0
    let Z : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j => if i = j then if i = 0 then 1 else -1 else 0
    let tensor : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun A B (i, k) (j, l) => A i j * B k l
    let bell : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun (i, j) (k, l) =>
        (1 / (Real.sqrt 2 : ℂ)) *
          (if k = 0 ∧ l = 0 then
            if i = j then 1 else 0
          else if k = 0 ∧ l = 1 then
            if i ≠ j then 1 else 0
          else if k = 1 ∧ l = 0 then
            if i = j then if i = 0 then 1 else -1 else 0
          else
            if i = 0 ∧ j = 1 then 1
            else if i = 1 ∧ j = 0 then -1
            else 0)
    let bellCoord : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun Q u v =>
        ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          star (bell p u) * Q p q * bell q v
    let blocks : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun A C Cdag D (r, i) (s, j) =>
        if r = 0 ∧ s = 0 then A i j
        else if r = 0 ∧ s = 1 then C i j
        else if r = 1 ∧ s = 0 then Cdag i j
        else D i j
    let Nα : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      (a : ℂ) • tensor Y Id2 + (b : ℂ) • tensor Y X +
        (c : ℂ) • tensor Y Y + (t : ℂ) • tensor Y Z +
        (d : ℂ) • tensor Id2 Z + (e : ℂ) • tensor X Z +
        (f : ℂ) • tensor Z Z
    let C : Matrix (Fin 2) (Fin 2) ℂ :=
      (Complex.I * (b : ℂ)) • Id2 + (Complex.I * (a : ℂ)) • X -
        (Complex.I * (e : ℂ)) • Y + (d : ℂ) • Z
    let Cdag : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j => star (C j i)
    (bellCoord Nα =
        blocks
          ((t : ℂ) • Y + ((f - c : ℝ) : ℂ) • Z)
          C Cdag
          (-(t : ℂ) • Y + ((f + c : ℝ) : ℂ) • Z)) ∧
      (let ptrans : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
          Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
        fun Q (i, k) (j, l) => Q (i, l) (j, k)
       bellCoord (ptrans Nα) =
        blocks
          ((t : ℂ) • Y + ((f + c : ℝ) : ℂ) • Z)
          C Cdag
          (-(t : ℂ) • Y + ((f - c : ℝ) : ℂ) • Z))

def claim13510 : Prop :=
  ∀ (x g a b c t d e f : ℝ),
    let Id2 : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j => if i = j then 1 else 0
    let X : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j =>
        if i = 0 ∧ j = 1 then 1
        else if i = 1 ∧ j = 0 then 1
        else 0
    let Y : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j =>
        if i = 0 ∧ j = 1 then -Complex.I
        else if i = 1 ∧ j = 0 then Complex.I
        else 0
    let Z : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j => if i = j then if i = 0 then 1 else -1 else 0
    let tensor : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun A B (i, k) (j, l) => A i j * B k l
    let bell : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun (i, j) (k, l) =>
        (1 / (Real.sqrt 2 : ℂ)) *
          (if k = 0 ∧ l = 0 then
            if i = j then 1 else 0
          else if k = 0 ∧ l = 1 then
            if i ≠ j then 1 else 0
          else if k = 1 ∧ l = 0 then
            if i = j then if i = 0 then 1 else -1 else 0
          else
            if i = 0 ∧ j = 1 then 1
            else if i = 1 ∧ j = 0 then -1
            else 0)
    let fromBell : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun R p q =>
        ∑ u : Fin 2 × Fin 2, ∑ v : Fin 2 × Fin 2,
          bell p u * R u v * star (bell q v)
    let blocks : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun A C Cdag D (r, i) (s, j) =>
        if r = 0 ∧ s = 0 then A i j
        else if r = 0 ∧ s = 1 then C i j
        else if r = 1 ∧ s = 0 then Cdag i j
        else D i j
    let qvisBell : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      blocks
        (((x / 4 : ℝ) : ℂ) • Id2 - ((g / 4 : ℝ) : ℂ) • Y)
        0 0
        ((((4 + x) / 4 : ℝ) : ℂ) • Id2 - ((g / 4 : ℝ) : ℂ) • Y)
    let Qvis := fromBell qvisBell
    let Nα : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      (a : ℂ) • tensor Y Id2 + (b : ℂ) • tensor Y X +
        (c : ℂ) • tensor Y Y + (t : ℂ) • tensor Y Z +
        (d : ℂ) • tensor Id2 Z + (e : ℂ) • tensor X Z +
        (f : ℂ) • tensor Z Z
    let ptrans : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun Q (i, k) (j, l) => Q (i, l) (j, k)
    let Q := Qvis + Nα
    let Qt := Qvis + (t : ℂ) • tensor Y Z
    let ray : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
        (Fin 2 × Fin 2 → ℂ) → ℝ :=
      fun Q v => (∑ i : Fin 2 × Fin 2, star (v i) * (Matrix.mulVec Q v) i).re
    let lambdaMin : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ → ℝ :=
      fun Q =>
        sInf {r : ℝ | ∃ v : Fin 2 × Fin 2 → ℂ,
          (∑ i : Fin 2 × Fin 2, ‖v i‖ ^ 2 = 1) ∧ r = ray Q v}
    let μ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ → ℝ :=
      fun Q => min (lambdaMin Q) (lambdaMin (ptrans Q))
    let m₀ : ℝ := (x - |g|) / 4
    let Δ : ℝ := m₀ - μ Q
    μ Q ≤ μ Qt ∧
      μ Qt = m₀ - |t| ∧
      Δ = m₀ - μ (Qvis + Nα) ∧
      Δ ≥ |t|

def claim13512 : Prop :=
  ∀ (x g a b c t d e f : ℝ),
    let Id2 : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j => if i = j then 1 else 0
    let X : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j =>
        if i = 0 ∧ j = 1 then 1
        else if i = 1 ∧ j = 0 then 1
        else 0
    let Y : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j =>
        if i = 0 ∧ j = 1 then -Complex.I
        else if i = 1 ∧ j = 0 then Complex.I
        else 0
    let Z : Matrix (Fin 2) (Fin 2) ℂ :=
      fun i j => if i = j then if i = 0 then 1 else -1 else 0
    let tensor : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun A B (i, k) (j, l) => A i j * B k l
    let bell : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun (i, j) (k, l) =>
        (1 / (Real.sqrt 2 : ℂ)) *
          (if k = 0 ∧ l = 0 then
            if i = j then 1 else 0
          else if k = 0 ∧ l = 1 then
            if i ≠ j then 1 else 0
          else if k = 1 ∧ l = 0 then
            if i = j then if i = 0 then 1 else -1 else 0
          else
            if i = 0 ∧ j = 1 then 1
            else if i = 1 ∧ j = 0 then -1
            else 0)
    let fromBell : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun R p q =>
        ∑ u : Fin 2 × Fin 2, ∑ v : Fin 2 × Fin 2,
          bell p u * R u v * star (bell q v)
    let blocks : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun A C Cdag D (r, i) (s, j) =>
        if r = 0 ∧ s = 0 then A i j
        else if r = 0 ∧ s = 1 then C i j
        else if r = 1 ∧ s = 0 then Cdag i j
        else D i j
    let qvisBell : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      blocks
        ((((x / 4 : ℝ) : ℂ) • Id2 - ((g / 4 : ℝ) : ℂ) • Y))
        0 0
        ((((4 + x) / 4 : ℝ) : ℂ) • Id2 - ((g / 4 : ℝ) : ℂ) • Y)
    let Qvis := fromBell qvisBell
    let Nα : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      (a : ℂ) • tensor Y Id2 + (b : ℂ) • tensor Y X +
        (c : ℂ) • tensor Y Y + (t : ℂ) • tensor Y Z +
        (d : ℂ) • tensor Id2 Z + (e : ℂ) • tensor X Z +
        (f : ℂ) • tensor Z Z
    let ptrans : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun Q (i, k) (j, l) => Q (i, l) (j, k)
    let Q := Qvis + Nα
    let ray : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
        (Fin 2 × Fin 2 → ℂ) → ℝ :=
      fun Q v => (∑ i : Fin 2 × Fin 2, star (v i) * (Matrix.mulVec Q v) i).re
    let lambdaMin : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ → ℝ :=
      fun Q =>
        sInf {r : ℝ | ∃ v : Fin 2 × Fin 2 → ℂ,
          (∑ i : Fin 2 × Fin 2, ‖v i‖ ^ 2 = 1) ∧ r = ray Q v}
    let μ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ → ℝ :=
      fun Q => min (lambdaMin Q) (lambdaMin (ptrans Q))
    let m₀ : ℝ := (x - |g|) / 4
    let Δ : ℝ := m₀ - μ Q
    let A : ℝ := |g| / 4
    let sgn : ℝ → ℝ := fun z => if z < 0 then -1 else if z > 0 then 1 else 0
    let rdir : ℝ → ℝ → ℝ → ℝ :=
      fun τ γ φ => Real.sqrt ((τ - sgn g * A) ^ 2 + (φ - γ) ^ 2)
    let rppt : ℝ → ℝ → ℝ → ℝ :=
      fun τ γ φ => Real.sqrt ((τ + sgn g * A) ^ 2 + (φ + γ) ^ 2)
    let Ddiag : ℝ → ℝ → ℝ → ℝ :=
      fun τ γ φ => max (rdir τ γ φ) (rppt τ γ φ) - A
    Δ ≥ Ddiag t c f ∧
      Ddiag t c f ≥ 0 ∧
      (Ddiag t c f = 0 ↔ t = 0 ∧ c = 0 ∧ f = 0) ∧
      Ddiag t 0 0 = |t| ∧
      Ddiag 0 c f = Real.sqrt (A ^ 2 + (|c| + |f|) ^ 2) - A

end MathlibPlus.Open.Research
