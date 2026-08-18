import MathlibPlus.Open.ResearchFormalization.R0992Claim28032

namespace MathlibPlus.Open.ResearchFormalization.R0992Claim28030

noncomputable section

open MathlibPlus.Open.Research.OrbitalCriteria
open MathlibPlus.Open.ResearchFormalization.R0992Claim28032

/-- The six-dimensional coefficient-table carrier used by the fixed quadratic
transporter.  A normalized rank-one table is the admitted affine-line slice:
its value at the origin is zero and its image is contained in a one-dimensional
linear subspace (the zero table is included). -/
def normalizedRankOneTable (F : Plane → Fibre) : Prop :=
  F 0 = 0 ∧
    ∃ v : Fibre, v ≠ 0 ∧ ∀ x : Plane, ∃ a : F3, F x = a • v

def direction100 : Fibre := ![(1 : F3), 0, 0]

def direction111 : Fibre := ![(1 : F3), 1, 1]

def direction121 : Fibre := ![(1 : F3), 2, 1]

/-- The six displayed normalized tables, with the two scalar signs in each
of the three listed directions. -/
def exceptionalTables : Set (Plane → Fibre) :=
  {F |
    F = (fun x : Plane => x 0 • direction100) ∨
      F = (fun x : Plane => (-(x 0)) • direction100) ∨
      F = (fun x : Plane => (x 0 + x 1) • direction111) ∨
      F = (fun x : Plane => (-(x 0 + x 1)) • direction111) ∨
      F = (fun x : Plane => (x 0 - x 1) • direction121) ∨
      F = (fun x : Plane => (-(x 0 - x 1)) • direction121)}

def generatedGroupFor (F : Plane → Fibre) : Subgroup (Equiv.Perm E) :=
  generatedGroup (transporter F)

def exactTwoClosureFor (F : Plane → Fibre) : Set (Equiv.Perm E) :=
  twoClosureOf (generatedGroupFor F : Set (Equiv.Perm E))

/-- Failure of the displayed transporter to fix every point-stabilizer
suborbit of the generated group. -/
def failsSuborbitFixation (F : Plane → Fibre) : Prop :=
  ¬ fixesStabilizerOrbits (transporter F)
      (generatedGroupFor F : Set (Equiv.Perm E)) (0 : E)

def conjugatesRegularPair (F : Plane → Fibre) (c : Equiv.Perm E) : Prop :=
  Set.image (fun h : Equiv.Perm E => c⁻¹ * h * c)
      (translationGroup : Set (Equiv.Perm E)) =
    conjugateSet (transporter F) (translationGroup : Set (Equiv.Perm E))

def exceptionalClosureData (F : Plane → Fibre) : Prop :=
  Nat.card (generatedGroupFor F) = 3 ^ 9 ∧
    Set.ncard (exactTwoClosureFor F) = 3 ^ 11 ∧
      transporter F ∉ exactTwoClosureFor F ∧
        ∃ c : Equiv.Perm E,
          c ∈ exactTwoClosureFor F ∧ conjugatesRegularPair F c

/-- Claim 28030: the six normalized rank-one tables that fail the displayed
suborbit-fixation test are exactly the three listed directions with both
scalar signs; each has generated order `3^9`, exact two-closure order `3^11`,
exterior displayed transporter, and an alternate conjugator in that closure. -/
def claim28030 : Prop :=
  {F : Plane → Fibre |
      normalizedRankOneTable F ∧ failsSuborbitFixation F} = exceptionalTables ∧
    Set.ncard
        {F : Plane → Fibre |
          normalizedRankOneTable F ∧ failsSuborbitFixation F} = 6 ∧
      ∀ F : Plane → Fibre, F ∈ exceptionalTables → exceptionalClosureData F

end
end MathlibPlus.Open.ResearchFormalization.R0992Claim28030
