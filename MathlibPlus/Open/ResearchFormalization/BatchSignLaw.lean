import Mathlib

noncomputable section
open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization

/-! The admitted R-4105 sign-law statements have a fully specified finite
carrier, so the law and both output claims can be stated without opaque data. -/

abbrev SignTriple := Fin 3 → Bool
abbrev RademacherCube5 := Fin 5 → Bool

def signLawMass (s : SignTriple) : ℝ :=
  if s = (fun _ => true) ∨ s = (fun _ => false) then
    (13 : ℝ) / 32
  else
    (1 : ℝ) / 32

def signValue (b : Bool) : ℝ := if b then 1 else -1

def mu (s : SignTriple) : ℝ :=
  (∑ i : Fin 3, signValue (s i)) / 3

def expectation (p : SignTriple → ℝ) (f : SignTriple → ℝ) : ℝ :=
  ∑ s : SignTriple, p s * f s

def variance (p : SignTriple → ℝ) (f : SignTriple → ℝ) : ℝ :=
  let m := expectation p f
  expectation p (fun s => (f s - m) ^ 2)

def agreesOn (I : Finset (Fin 3)) (s t : SignTriple) : Prop :=
  ∀ i ∈ I, s i = t i

def conditionalMean (p : SignTriple → ℝ) (f : SignTriple → ℝ)
    (I : Finset (Fin 3)) (s : SignTriple) : ℝ :=
  (∑ t : SignTriple,
      if agreesOn I s t then p t * f t else 0) /
    (∑ t : SignTriple,
      if agreesOn I s t then p t else 0)

def conditionalVariance (p : SignTriple → ℝ) (f : SignTriple → ℝ)
    (I : Finset (Fin 3)) : ℝ :=
  ∑ s : SignTriple,
    p s * (f s - conditionalMean p f I s) ^ 2

def exchangeableSignLawMoments : Prop :=
  expectation signLawMass mu = 0 ∧
  variance signLawMass mu = (5 : ℝ) / 6 ∧
  ∀ σ : Equiv.Perm (Fin 3),
    conditionalVariance signLawMass mu ({σ 0} : Finset (Fin 3)) =
        (5 : ℝ) / 36 ∧
    conditionalVariance signLawMass mu ({σ 0, σ 1} : Finset (Fin 3)) =
        (5 : ℝ) / 126

def outputTriple (f₀ f₁ f₂ : RademacherCube5 → Bool)
    (u : RademacherCube5) : SignTriple :=
  ![f₀ u, f₁ u, f₂ u]

def outputCount (f₀ f₁ f₂ : RademacherCube5 → Bool)
    (s : SignTriple) : ℕ :=
  (Finset.univ.filter (fun u => outputTriple f₀ f₁ f₂ u = s)).card

def targetOutputCount (s : SignTriple) : ℕ :=
  if s = (fun _ => true) ∨ s = (fun _ => false) then 13 else 1

def booleanCubeRealization : Prop :=
  ∃ f₀ f₁ f₂ : RademacherCube5 → Bool,
    ∀ s : SignTriple, outputCount f₀ f₁ f₂ s = targetOutputCount s

end MathlibPlus.Open.ResearchFormalization
