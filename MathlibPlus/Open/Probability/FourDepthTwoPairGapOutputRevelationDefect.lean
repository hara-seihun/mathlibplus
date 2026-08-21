import Mathlib

namespace MathlibPlus.Open.Probability

/-- An explicit common/private selector cube witnesses that output-only
revelation can have root-inclusive area `961/960` for every legal adaptive
ordering of four component outputs.  The proposition is a finite registry
node; its proof is intentionally left to the finite-fibre formalization lane. -/
def fourDepthTwoPairGapOutputRevelationDefect : Prop :=
  let Ω := Fin 6 → Bool
  let sign : Bool → ℚ := fun b => if b then 1 else -1
  let branch : Fin 4 → Fin 6 := fun i => ⟨2 + i.1, by omega⟩
  let output : Fin 4 → Ω → Bool := fun i ω =>
    if ω 0 then ω (branch i) else ω 1
  let target : Ω → ℚ := fun ω =>
    (∑ i : Fin 4, sign (output i ω)) / (4 : ℚ)
  let mean : (Ω → ℚ) → ℚ := fun f =>
    (∑ ω : Ω, f ω) / (Fintype.card Ω : ℚ)
  let variance : (Ω → ℚ) → ℚ := fun f =>
    let μ := mean f
    mean (fun ω => (f ω - μ) ^ 2)
  let meanOn : Finset Ω → (Ω → ℚ) → ℚ := fun s f =>
    (∑ ω ∈ s, f ω) / (s.card : ℚ)
  let varianceOn : Finset Ω → (Ω → ℚ) → ℚ := fun s f =>
    let μ := meanOn s f
    meanOn s (fun ω => (f ω - μ) ^ 2)
  let Policy := Fin 4 × (Bool → Fin 4) × (Bool → Bool → Fin 4)
  let entry : Policy → Ω → Fin 3 → Fin 4 × Bool := fun p ω k =>
    match k.1 with
    | 0 => (p.1, output p.1 ω)
    | 1 =>
        let j := p.2.1 (output p.1 ω)
        (j, output j ω)
    | _ =>
        let j := p.2.1 (output p.1 ω)
        let l := p.2.2 (output p.1 ω) (output j ω)
        (l, output l ω)
  let sameTranscript : Policy → Ω → Ω → Fin 4 → Prop :=
    fun p ω ω' m =>
      ∀ k : Fin 3, k.1 < m.1 → entry p ω k = entry p ω' k
  let fiber : Policy → Ω → Fin 4 → Finset Ω := fun p ω m =>
    Finset.univ.filter (fun ω' => sameTranscript p ω ω' m)
  let expectedVariance : Policy → Fin 4 → ℚ := fun p m =>
    mean (fun ω => varianceOn (fiber p ω m) target)
  let area : Policy → ℚ := fun p =>
    variance target + expectedVariance p 1 + expectedVariance p 2 +
      expectedVariance p 3
  let legal : Policy → Prop := fun p =>
    (∀ a : Bool, p.2.1 a ≠ p.1) ∧
      (∀ a b : Bool,
        p.2.2 a b ≠ p.1 ∧ p.2.2 a b ≠ p.2.1 a)
  let selectorDisplay : Prop :=
    ∀ (i : Fin 4) (ω : Ω),
      output i ω = if ω 0 then ω (branch i) else ω 1
  let pairwiseDistinct : Prop :=
    ∀ i j : Fin 4, i ≠ j → ∃ ω : Ω, output i ω ≠ output j ω
  let centered : Prop :=
    ∀ i : Fin 4, mean (fun ω => sign (output i ω)) = 0
  let pairCorrelation : Prop :=
    ∀ i j : Fin 4, i ≠ j →
      mean (fun ω => sign (output i ω) * sign (output j ω)) = (1 : ℚ) / 2
  selectorDisplay ∧
    pairwiseDistinct ∧
    centered ∧
    pairCorrelation ∧
    (∀ p : Policy, legal p → area p = (961 : ℚ) / 960) ∧
    (1 : ℚ) < 961 / 960

end MathlibPlus.Open.Probability
