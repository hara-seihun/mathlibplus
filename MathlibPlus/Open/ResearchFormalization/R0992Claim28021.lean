import MathlibPlus.Open.ResearchFormalization.R0992Claim28032

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0992Claim28021

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0992Claim28032
open MathlibPlus.Open.Research.OrbitalCriteria

def onePlaneTable (x₀ : Plane) (lam : Fibre) : Plane → Fibre :=
  fun x => if x = x₀ then lam else 0

def onePlaneGroup (x₀ : Plane) (lam : Fibre) :
    Subgroup (Equiv.Perm E) :=
  generatedGroup (transporter (onePlaneTable x₀ lam))

def onePlaneTransporter (x₀ : Plane) (lam : Fibre) : Equiv.Perm E :=
  transporter (onePlaneTable x₀ lam)

noncomputable def groupCard (G : Subgroup (Equiv.Perm E)) : ℕ :=
  letI := Classical.decEq (Equiv.Perm E)
  letI := Classical.propDecidable
  (Finset.univ.filter (fun g : Equiv.Perm E =>
    g ∈ (G : Set (Equiv.Perm E)))).card

noncomputable def pointStabilizerCard
    (G : Subgroup (Equiv.Perm E)) : ℕ :=
  letI := Classical.decEq (Equiv.Perm E)
  letI := Classical.propDecidable
  (Finset.univ.filter
    (fun g : Equiv.Perm E =>
      g ∈ (G : Set (Equiv.Perm E)) ∧ g 0 = 0)).card

noncomputable def stabilizerOrbitFinset
    (G : Subgroup (Equiv.Perm E)) (x : E) : Finset E :=
  letI := Classical.decEq E
  letI := Classical.propDecidable
  (Finset.univ.filter
    (fun y : E => y ∈ stabilizerOrbit (G : Set (Equiv.Perm E)) 0 x))

noncomputable def pointStabilizerSuborbits
    (G : Subgroup (Equiv.Perm E)) : Finset (Finset E) :=
  letI := Classical.decEq E
  (Finset.univ : Finset E).image (stabilizerOrbitFinset G)

noncomputable def histogramOneThreeTwentySeven
    (G : Subgroup (Equiv.Perm E)) : Prop :=
  letI := Classical.decEq E
  let O := pointStabilizerSuborbits G
  O.card = 69 ∧
    (O.filter (fun s => s.card = 1)).card = 27 ∧
      (O.filter (fun s => s.card = 3)).card = 18 ∧
        (O.filter (fun s => s.card = 27)).card = 24

def normalizesGroup
    (q : Equiv.Perm E) (G : Subgroup (Equiv.Perm E)) : Prop :=
  ∀ h : Equiv.Perm E,
    h ∈ (G : Set (Equiv.Perm E)) ↔
      q⁻¹ * h * q ∈ (G : Set (Equiv.Perm E))

/-- Claim 28021: the exact one-plane-supported 234-table census on the
    `F₃ ⊕ F₃² ⊕ F₃³` transporter carrier. -/
def exactGroupOrbitData_claim28021 : Prop :=
  Nat.card (Plane × {lam : Fibre // lam ≠ 0}) = 234 ∧
    ∀ (x₀ : Plane) (lam : Fibre), lam ≠ 0 →
      let q := onePlaneTransporter x₀ lam
      let G := onePlaneGroup x₀ lam
      groupCard G = 3 ^ 22 ∧
        pointStabilizerCard G = 3 ^ 16 ∧
          histogramOneThreeTwentySeven G ∧
            normalizesGroup q G ∧
              fixesStabilizerOrbits q
                (G : Set (Equiv.Perm E)) 0 ∧
                q ∉ (G : Set (Equiv.Perm E))

end

end MathlibPlus.Open.ResearchFormalization.R0992Claim28021
