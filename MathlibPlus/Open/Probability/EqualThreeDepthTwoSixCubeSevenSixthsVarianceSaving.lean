import Mathlib

namespace MathlibPlus.Open.Probability

noncomputable section

/--
On the uniform six-sign cube, every equal average of three Boolean functions
of deterministic decision-tree depth at most two satisfies the sharp
variance-saving Bellman inequality with coefficient seven sixths and singleton
Fourier credit. A triangle of shared-leaf selectors attains equality.
-/
def equalThreeDepthTwoSixCubeSevenSixthsVarianceSaving : Prop :=
  let Ω := Fin 6 → Bool
  let Strategy := List Bool → Fin 6
  let transcript : Strategy → Ω → ℕ → List Bool := fun q x m =>
    Nat.rec [] (fun _ answers => answers ++ [x (q answers)]) m
  let Fresh : Strategy → Prop := fun q =>
    ∀ (x : Ω) (a b : ℕ), a < b → b < 6 →
      q (transcript q x a) ≠ q (transcript q x b)
  let TreeCert : (Ω → Bool) → Strategy → (List Bool → Bool) →
      (List Bool → Bool) → (Ω → ℕ) → Prop := fun h q done out stop =>
    Fresh q ∧
    (∀ x, stop x ≤ 6) ∧
    (∀ x, done (transcript q x (stop x)) = true) ∧
    (∀ x m, m < stop x → done (transcript q x m) = false) ∧
    (∀ x, h x = out (transcript q x (stop x)))
  let qCost : (Ω → Bool) → ℝ := fun h =>
    sInf {c : ℝ | ∃ (q : Strategy) (done out : List Bool → Bool)
        (stop : Ω → ℕ),
      TreeCert h q done out stop ∧
      c = (∑ x : Ω, (stop x : ℝ)) / (2 : ℝ) ^ 6}
  let DepthAtMostTwo : (Ω → Bool) → Prop := fun h =>
    ∃ (q : Strategy) (done out : List Bool → Bool) (stop : Ω → ℕ),
      TreeCert h q done out stop ∧ ∀ x, stop x ≤ 2
  let restrict : (Ω → Bool) → Fin 6 → Bool → Ω → Bool := fun h i b x =>
    h (Function.update x i b)
  let saving : (Ω → Bool) → Fin 6 → ℝ := fun h i =>
    qCost h - (qCost (restrict h i false) + qCost (restrict h i true)) / 2
  let sgn : Bool → ℝ := fun b => if b then 1 else -1
  let uniformMean : (Ω → ℝ) → ℝ := fun g =>
    (∑ x : Ω, g x) / (2 : ℝ) ^ 6
  let uniformVariance : (Ω → ℝ) → ℝ := fun g =>
    (∑ x : Ω, (g x) ^ 2) / (2 : ℝ) ^ 6 - uniformMean g ^ 2
  let singleton : (Ω → ℝ) → Fin 6 → ℝ := fun g i =>
    (∑ x : Ω, g x * sgn (x i)) / (2 : ℝ) ^ 6
  let target : (Fin 3 → Ω → Bool) → Ω → ℝ := fun h x =>
    (∑ j, sgn (h j x)) / 3
  let universal : Prop :=
    ∀ h : Fin 3 → Ω → Bool,
      (∀ j, DepthAtMostTwo (h j)) →
      ∃ i : Fin 6,
        uniformVariance (target h) ≤
          (7 / 6 : ℝ) * ((∑ j, saving (h j) i) / 3) +
            singleton (target h) i ^ 2
  let T0 : Ω → Bool := fun x => if x 3 then x 4 else x 5
  let T1 : Ω → Bool := fun x => if x 1 then x 2 else x 5
  let T2 : Ω → Bool := fun x => if x 0 then x 2 else x 4
  let sharpTarget : Ω → ℝ := fun x =>
    (sgn (T0 x) + sgn (T1 x) + sgn (T2 x)) / 3
  let sharp : Prop :=
    DepthAtMostTwo T0 ∧ DepthAtMostTwo T1 ∧ DepthAtMostTwo T2 ∧
    uniformVariance sharpTarget = 1 / 2 ∧
    (∀ i : Fin 6, (saving T0 i + saving T1 i + saving T2 i) / 3 = 1 / 3) ∧
    singleton sharpTarget 2 ^ 2 = 1 / 9 ∧
    singleton sharpTarget 4 ^ 2 = 1 / 9 ∧
    singleton sharpTarget 5 ^ 2 = 1 / 9
  universal ∧ sharp

end

end MathlibPlus.Open.Probability
