import MathlibPlus.Open.ResearchFormalization.GrowingOrbitTheoremClaim35101

namespace MathlibPlus.Open.ResearchFormalization.Claim35085

open MathlibPlus.Open.ResearchFormalization.GrowingOrbitTheoremClaim35101

noncomputable section

abbrev DirectionalFamily35085 := DirectionalFamily
abbrev Vector35085 (n : ℕ) := Vector n

/-- The literal coordinate-dependent edge function in direction `i`. -/
def directionalFunction35085
    (f : DirectionalFamily35085) (n : ℕ) (i : Fin n) : Vector35085 n → Bool :=
  f n i

/-- The directional probability `p_i`, represented by the exact uniform
coordinate-zero density carrier from Claim 35101. -/
def directionalMean35085
    (f : DirectionalFamily35085) (n : ℕ) (i : Fin n) : ℝ :=
  directionalDensity i (f n i)

/-- The literal translation orbit on the exact quotient domain `x_i=0`. -/
def directionalOrbit35085 {n : ℕ} (i : Fin n)
    (g : Vector35085 n → Bool) : Set (Vector35085 n → Bool) :=
  {h | ∃ v : Vector35085 n, v i = 0 ∧
    h = translatedRestriction (i := i) g v}

noncomputable def directionalOrbitCard35085 {n : ℕ} (i : Fin n)
    (g : Vector35085 n → Bool) : ℕ :=
  Nat.card {h : Vector35085 n → Bool // h ∈ directionalOrbit35085 i g}

/-- The target class of Claim 35085: exact C4-freeness together with the
literal directional orbit cap for every dimension and direction. -/
def c4FreeOrbitCappedFamily35085
    (f : DirectionalFamily35085) (M : ℕ → ℕ) : Prop :=
  familyC4Free f ∧ familyOrbitCapped f M

end

end MathlibPlus.Open.ResearchFormalization.Claim35085
