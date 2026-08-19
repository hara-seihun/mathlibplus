import MathlibPlus.Open.ResearchFormalization.R1414Claims36936_36937_36939

namespace MathlibPlus.Open.ResearchFormalization.R1414Claim36934

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1414

abbrev CrownVertex (n : ℕ) := Fin 2 × Fin n

/-- The standard crown adjacency relation on two labelled sides. -/
def crownAdj {n : ℕ} (x y : CrownVertex n) : Prop :=
  x.1 ≠ y.1 ∧ x.2 ≠ y.2

def crownGraph (n : ℕ) : SimpleGraph (CrownVertex n) :=
  SimpleGraph.fromRel (crownAdj (n := n))

/-- The opposite side of a crown vertex. -/
def finTwoFlip (s : Fin 2) : Fin 2 :=
  if s = 0 then 1 else 0

/-- The unique opposite-side nonneighbor paired with a crown vertex. -/
def crownPartner {n : ℕ} (x : CrownVertex n) : CrownVertex n :=
  (finTwoFlip x.1, x.2)

def crownOppositeNonneighbor {n : ℕ}
    (x y : CrownVertex n) : Prop :=
  x.1 ≠ y.1 ∧ ¬ crownAdj x y

/-- The perfect-pairing assertion keeps uniqueness on the nonneighbor
relation itself; the displayed partner is identified separately. -/
def crownPerfectPairing (n : ℕ) : Prop :=
  (∀ x : CrownVertex n,
    ∃! y : CrownVertex n, crownOppositeNonneighbor x y) ∧
    (∀ x y : CrownVertex n,
      crownOppositeNonneighbor x y → y = crownPartner x)

/-- Intrinsic recognition of the crown bipartition by every graph
automorphism, up to one global side permutation. -/
def crownBipartitionIntrinsic (n : ℕ) : Prop :=
  ∀ e : Equiv.Perm (CrownVertex n),
    r1414GraphAutomorphism (crownGraph n) e →
      ∃ c : R1414Two,
        ∀ x : CrownVertex n, (e x).1 = c x.1

/-- Intrinsic preservation of the opposite-side nonneighbor pairing. -/
def crownPairingIntrinsic (n : ℕ) : Prop :=
  ∀ e : Equiv.Perm (CrownVertex n),
    r1414GraphAutomorphism (crownGraph n) e →
      ∀ x : CrownVertex n,
        e (crownPartner x) = crownPartner (e x)

/-- A proof-free carrier for an isomorphism between a model group and the
full graph-automorphism group: the map is injective, multiplicative, has
only graph automorphisms in its image, and exhausts all graph automorphisms. -/
def graphAutomorphismModel {V M : Type*} [Group M]
    (G : SimpleGraph V) : Prop :=
  ∃ f : M → Equiv.Perm V,
    (∀ m : M, r1414GraphAutomorphism G (f m)) ∧
      (∀ a b : M, f (a * b) = f a * f b) ∧
      (∀ a b : M, f a = f b → a = b) ∧
      (∀ e : Equiv.Perm V,
        r1414GraphAutomorphism G e → ∃ m : M, f m = e)

/-- Claim 36934: connectedness, intrinsic crown pairing/bipartition, and the
full automorphism models for the crown and its independent two-point blow-up. -/
def claim36934 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    SimpleGraph.Connected (crownGraph n) ∧
      crownPerfectPairing n ∧
      crownBipartitionIntrinsic n ∧
      crownPairingIntrinsic n ∧
      graphAutomorphismModel (M := R1414Top n) (crownGraph n) ∧
      graphAutomorphismModel (M := R1414Semidirect n) (r1414YGraph n)

end

end MathlibPlus.Open.ResearchFormalization.R1414Claim36934
