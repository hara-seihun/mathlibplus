import Mathlib

namespace MathlibPlus.Open.ProjectsResearch.R1215

abbrev C7Squared := ZMod 7 × ZMod 7

def IsLine (H : AddSubgroup C7Squared) : Prop :=
  Nat.card H = 7

def translate (B : Finset C7Squared) (d : C7Squared) : Finset C7Squared :=
  B.image (fun b => b + d)

def differenceMultiplicity (B : Finset C7Squared) (d : C7Squared) : ℕ :=
  (B.filter (fun b => b - d ∈ B)).card

def translateIntersectionCard (B : Finset C7Squared) (d : C7Squared) : ℕ :=
  (B ∩ translate B d).card

def RelativeDifferenceSet (B : Finset C7Squared) (H : AddSubgroup C7Squared) : Prop :=
  B.card = 7 ∧
    IsLine H ∧
      ∀ d : C7Squared,
        d ≠ 0 →
          (d ∈ H → differenceMultiplicity B d = 0) ∧
            (d ∉ H → differenceMultiplicity B d = 1)

def claim_30223 : Prop :=
  ∀ (B : Finset C7Squared) (H : AddSubgroup C7Squared),
    RelativeDifferenceSet B H →
      translateIntersectionCard B 0 = 7 ∧
        (∀ d : C7Squared, d ≠ 0 → d ∈ H → translateIntersectionCard B d = 0) ∧
          (∀ d : C7Squared, d ∉ H → translateIntersectionCard B d = 1)

def translateDisjointGraph (B : Finset C7Squared) : SimpleGraph C7Squared :=
  SimpleGraph.fromRel (fun g h => Disjoint (translate B g) (translate B h))

def sevenK7 : SimpleGraph (Fin 7 × Fin 7) :=
  SimpleGraph.fromRel (fun u v => u.2 = v.2 ∧ u.1 ≠ v.1)

def claim_30224 : Prop :=
  ∀ (B : Finset C7Squared) (H : AddSubgroup C7Squared),
    RelativeDifferenceSet B H →
      Fintype.card C7Squared = 49 ∧
        Nonempty (translateDisjointGraph B ≃g sevenK7) ∧
          ∀ g h : C7Squared,
            ¬SimpleGraph.Reachable (translateDisjointGraph B) g h →
              (translate B g ∩ translate B h).card = 1

def Planar (p : ℕ) (g : ZMod p → ZMod p) : Prop :=
  ∀ a : ZMod p, a ≠ 0 → Function.Bijective (fun x => g (x + a) - g x)

def IsAffineAutomorphism (f : C7Squared → C7Squared) : Prop :=
  Function.Bijective f ∧
    ∃ a b c d e k : ZMod 7,
      a * e - b * d ≠ 0 ∧
        ∀ z : C7Squared,
          f z =
            (a * z.1 + b * z.2 + c,
              d * z.1 + e * z.2 + k)

def verticalLine : Set C7Squared := {z | z.1 = 0}

def transversalGraph (g : ZMod 7 → ZMod 7) : Finset C7Squared :=
  Finset.univ.image (fun x => (x, g x))

def claim_30227 : Prop :=
  ∀ (B : Finset C7Squared) (K : AddSubgroup C7Squared),
    RelativeDifferenceSet B K →
      ∃ (f : C7Squared → C7Squared) (g : ZMod 7 → ZMod 7),
        IsAffineAutomorphism f ∧
          f '' (K : Set C7Squared) = verticalLine ∧
            Finset.image f B = transversalGraph g ∧ Planar 7 g

def claim_30228 : Prop :=
  (∀ (p : ℕ) (g : ZMod p → ZMod p),
      Nat.Prime p → Planar p g →
        ∃ a b c : ZMod p,
          a ≠ 0 ∧ ∀ x : ZMod p, g x = a * x ^ 2 + b * x + c) ∧
    (∀ (g : ZMod 7 → ZMod 7),
      Planar 7 g → g 0 = 0 →
        ∃ u v : ZMod 7, u ≠ 0 ∧ ∀ x : ZMod 7, g x = u * x ^ 2 + v * x)

def claim_30229 : Prop :=
  Nat.card {g : ZMod 7 → ZMod 7 // g 0 = 0} = 117649 ∧
    Nat.card {g : {g : ZMod 7 → ZMod 7 // g 0 = 0} // Planar 7 g.1} = 42 ∧
      ∀ (g : ZMod 7 → ZMod 7),
        g 0 = 0 →
          (Planar 7 g ↔
            ∃ u v : ZMod 7, u ≠ 0 ∧ ∀ x : ZMod 7, g x = u * x ^ 2 + v * x)

end MathlibPlus.Open.ProjectsResearch.R1215
