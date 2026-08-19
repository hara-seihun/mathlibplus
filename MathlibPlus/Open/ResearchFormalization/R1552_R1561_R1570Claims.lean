import MathlibPlus.Open.ResearchFormalization.R1552HomogeneousQuadraticFamily39166
import MathlibPlus.Open.ResearchFormalization.R1066Claim29967
import MathlibPlus.Open.ResearchFormalization.R1398_R1570

namespace MathlibPlus.Open.ResearchFormalization.R1552_R1561_R1570Claims

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1552HomogeneousQuadraticFamily39166
open MathlibPlus.Open.ResearchFormalization.R1066Claim29967
open MathlibPlus.Open.ResearchFormalization.R1398_R1570

/-- Claim 39167: the exact Record-6 row carrier has the two displayed
nondegenerate binary types, three lambda values, and six free ternary
quadratic coefficients, hence 4374 rows. -/
def familyCardinality_claim39167 : Prop :=
  Nat.card Row = 2 * 3 * 3 ^ 6 ∧
    Nat.card (Fin 2) = 2 ∧
    Nat.card F3 = 3 ∧
    Nat.card (Fin 6 → F3) = 3 ^ 6 ∧
    (∀ (q : Fin 2) (lambda : F3) (coeff : Fin 6 → F3)
      (x : State),
      rowTransporter (q, lambda, coeff) x =
        familyTransporter q lambda coeff x)

/-- Claim 39211: the exact `D = F₃²` fiber carrier has the sharp
`GL(2,3)` basis action, and that action is retained through the displayed
base chart, translations, value assignments, projective functionals, and
canonical/literal row counts. -/
def gl2ThreeSymmetryReduction_claim39211 : Prop :=
  let D := Base
  let B := Fin 3 → ZMod 3
  let independent : D → D → Prop := fun v w =>
    ∀ c d : ZMod 3, c • v + d • w = 0 → c = 0 ∧ d = 0
  let independentPairs :=
    {p : D × D // independent p.1 p.2}
  let baseChart : B → B := fun t =>
    ![t 0, t 1, t 2 + if t 1 = 2 then 1 else 0]
  let fiberLift : GL2_3 → Equiv.Perm (D × B) := fun L =>
    Equiv.prodCongr L.toEquiv (Equiv.refl B)
  let baseLift : (D × B) → (D × B) := fun x => (x.1, baseChart x.2)
  let valueLift : (B → D) → (D × B) → (D × B) := fun s x =>
    (x.1 + s x.2, baseChart x.2)
  let projectiveFunctionals : Fin 4 → D → ZMod 3 := fun i =>
    ![ (fun x => x 0),
       (fun x => x 1),
       (fun x => x 0 + x 1),
       (fun x => x 0 + 2 * x 1) ] i
  let canonicalSupports :=
    {S : Finset B // S.card = 2 ∧ ∀ t ∈ S, t ≠ 0}
  let literalRows :=
    {p : Finset B × (B → D) //
      p.1.card = 2 ∧
      (∀ t ∈ p.1, t ≠ 0) ∧
      (∀ t : B, p.2 t ≠ 0 ↔ t ∈ p.1) ∧
      (∀ a ∈ p.1, ∀ b ∈ p.1, a ≠ b →
        independent (p.2 a) (p.2 b))}
  Nat.card GL2_3 = 48 ∧
    Nat.card independentPairs = 48 ∧
    (∀ p q : independentPairs,
      ∃! L : GL2_3, L p.1.1 = q.1.1 ∧ L p.1.2 = q.1.2) ∧
    (∀ (L : GL2_3) (x : D × B),
      fiberLift L (baseLift x) = baseLift (fiberLift L x)) ∧
    (∀ (L : GL2_3) (a : D × B) (x : D × B),
      fiberLift L (a + x) =
        (L a.1, a.2) + fiberLift L x) ∧
    (∀ (L : GL2_3) (s : B → D) (x : D × B),
      fiberLift L (valueLift s x) =
        valueLift (fun t => L (s t)) (fiberLift L x)) ∧
    (∀ L : GL2_3, ∃ π : Fin 4 ≃ Fin 4,
      ∀ i : Fin 4, ∃ c : ZMod 3, c ≠ 0 ∧
        ∀ x : D,
          projectiveFunctionals i (L x) =
            c * projectiveFunctionals (π i) x) ∧
    Nat.card canonicalSupports = 325 ∧
    Nat.card literalRows = 15600 ∧
    (∀ (a b : B), a ≠ 0 → b ≠ 0 → a ≠ b →
      ∀ s : B → D,
        (∀ t : B, s t ≠ 0 ↔ t = a ∨ t = b) →
        independent (s a) (s b) →
        ∃ L : GL2_3,
          s a = L (![1, 0] : D) ∧ s b = L (![0, 1] : D))

/-- Claim 39261: the exact inverse-closed, identity-free valency-20
connection-set carrier on `C₂³ × C₉` has the admitted cardinality. -/
def valency20ConnectionSetCount_claim39261 : Prop :=
  Nat.card
      {S : Finset CayleyCarrier //
        0 ∉ S ∧ S.card = 20 ∧
          ∀ x : CayleyCarrier, x ∈ S ↔ -x ∈ S} =
    1045238532

end

end MathlibPlus.Open.ResearchFormalization.R1552_R1561_R1570Claims
