import MathlibPlus.Open.ResearchFormalization.R0992Claim28032

namespace MathlibPlus.Open.ResearchFormalization.R0992Claim28027

noncomputable section

abbrev F3 := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.F3
abbrev Plane := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.Plane
abbrev Fibre := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.Fibre
abbrev E := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.E

open MathlibPlus.Open.ResearchFormalization.R0992Claim28032
open MathlibPlus.Open.Research.OrbitalCriteria

/-- A table with the displayed two-point support presentation. -/
def twoSupportTable (x y : Plane) (lam mu : Fibre) : Plane → Fibre :=
  fun z => if z = x then lam else if z = y then mu else 0

def supportExactly (F : Plane → Fibre) (S : Set Plane) : Prop :=
  ∀ x : Plane, F x ≠ 0 ↔ x ∈ S

def twoSupported (F : Plane → Fibre) : Prop :=
  ∃ S : Set Plane, S.Finite ∧ S.ncard = 2 ∧ supportExactly F S

/-- Exact normalization of the generated group by the displayed transporter. -/
def normalizesGeneratedGroup (q : Equiv.Perm E) : Prop :=
  ∀ h : Equiv.Perm E,
    h ∈ (generatedGroup q : Set (Equiv.Perm E)) ↔
      q⁻¹ * h * q ∈ (generatedGroup q : Set (Equiv.Perm E))

def normalizationFailure (F : Plane → Fibre) : Prop :=
  ∃ x y : Plane, ∃ lam mu : Fibre,
    x ≠ y ∧ lam ≠ 0 ∧ mu ≠ 0 ∧ F = twoSupportTable x y lam mu ∧
      ¬ normalizesGeneratedGroup (transporter F)

def veroneseLine (d : Plane) : Fibre :=
  ![d 1 ^ 2, -(d 0 * d 1), d 0 ^ 2]

def exactTwoSupportObstruction (x y : Plane) (lam mu : Fibre) : Prop :=
  let F := twoSupportTable x y lam mu
  let q := transporter F
  (¬ normalizesGeneratedGroup q ↔
    (mu = -lam ∧
      ¬ ∃ t : F3, t ≠ 0 ∧ lam = t • veroneseLine (y - x)))

/-- Claim 28027: the normalization obstruction is the stated Veronese-line
condition, with the per-support-pair, total-failure, and all-transporter
censuses, while every two-support transporter fixes every suborbit and lies in
the exact 2-closure. -/
def exactTwoSupportNormalizationObstruction_claim28027 : Prop :=
  (∀ x y : Plane, ∀ lam mu : Fibre,
    x ≠ y → lam ≠ 0 → mu ≠ 0 → exactTwoSupportObstruction x y lam mu) ∧
    (∀ S : Set Plane, S.Finite → S.ncard = 2 →
      Nat.card {F : Plane → Fibre //
        supportExactly F S ∧ normalizationFailure F} = 24) ∧
    Nat.card {F : Plane → Fibre //
      twoSupported F ∧ normalizationFailure F} = 864 ∧
    24 * 36 = (864 : ℕ) ∧
    Nat.card {F : Plane → Fibre // twoSupported F} = 24336 ∧
    Nat.choose 9 2 * 26 ^ 2 = (24336 : ℕ) ∧
    (∀ F : Plane → Fibre, twoSupported F →
      let q := transporter F
      fixesStabilizerOrbits q (generatedGroup q : Set (Equiv.Perm E)) 0 ∧
        q ∈ twoClosureOf (generatedGroup q : Set (Equiv.Perm E)))

end
end MathlibPlus.Open.ResearchFormalization.R0992Claim28027
