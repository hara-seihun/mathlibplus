import MathlibPlus.Open.ResearchFormalizationBatch.R0667

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0667Claim29491

open MathlibPlus.Open.ResearchFormalizationBatch.R0667

/-- The completed-root maps are stored as total maps to `Option B`: the two
factor roots are sent to `none`, while all other values record the core
isomorphisms into the deleted copy of `F`. -/
structure CompleteIncidenceData
    {B P K : Type*}
    (F : SimpleGraph B) (Pgraph : SimpleGraph P) (Kgraph : SimpleGraph K)
    (S : Set B) where
  u : B
  v : B
  w : B
  p : P
  k : K
  phi : P → Option B
  psi : K → Option B

/-- The marked certificate retains the two maps into the apex extension, so
isomorphism maps remain multiplicity-bearing data rather than only existence
propositions. -/
structure MarkedTransverseData
    {B P K : Type*}
    (F : SimpleGraph B) (Pgraph : SimpleGraph P) (Kgraph : SimpleGraph K)
    (S : Set B) where
  u : Option B
  v : Option B
  w : Option B
  alpha : P → Option B
  beta : K → Option B

/-- Exact validity of a complete root-origin incidence certificate. -/
def completeIncidenceValid
    {B P K : Type*} [DecidableEq B] [DecidableEq P] [DecidableEq K]
    (F : SimpleGraph B) (Pgraph : SimpleGraph P) (Kgraph : SimpleGraph K)
    (S : Set B)
    (c : CompleteIncidenceData F Pgraph Kgraph S) : Prop :=
  c.u ≠ c.v ∧
    c.u ≠ c.w ∧
    c.v ≠ c.w ∧
    (∀ x : P, c.phi x = none ↔ x = c.p) ∧
    (∀ x : P, ∀ b : B, c.phi x = some b → b ≠ c.u) ∧
    (∀ x y : P, ∀ b : B,
      c.phi x = some b → c.phi y = some b → x = y) ∧
    (∀ b : B, b ≠ c.u → ∃ x : P, c.phi x = some b) ∧
    (∀ x y : P, ∀ bx bY : B,
      c.phi x = some bx → c.phi y = some bY →
        (Pgraph.Adj x y ↔ F.Adj bx bY)) ∧
    (∀ b : B,
      b ∈ S \ {c.u} ↔
        ∃ x : P, Pgraph.Adj c.p x ∧ c.phi x = some b) ∧
    (∀ x : K, c.psi x = none ↔ x = c.k) ∧
    (∀ x : K, ∀ b : B,
      c.psi x = some b → b ≠ c.v ∧ b ≠ c.w) ∧
    (∀ x y : K, ∀ b : B,
      c.psi x = some b → c.psi y = some b → x = y) ∧
    (∀ b : B, b ≠ c.v → b ≠ c.w → ∃ x : K, c.psi x = some b) ∧
    (∀ x y : K, ∀ bx bY : B,
      c.psi x = some bx → c.psi y = some bY →
        (Kgraph.Adj x y ↔ F.Adj bx bY)) ∧
    (∀ b : B,
      b ∈ S \ ({c.v, c.w} : Set B) ↔
        ∃ x : K, Kgraph.Adj c.k x ∧ c.psi x = some b)

/-- Exact validity of a marked transverse certificate at the fixed mask. -/
def markedTransverseValid
    {B P K : Type*} [Fintype B] [DecidableEq B] [DecidableEq P] [DecidableEq K]
    (F : SimpleGraph B) (Pgraph : SimpleGraph P) (Kgraph : SimpleGraph K)
    (S : Set B)
    (d : MarkedTransverseData F Pgraph Kgraph S) : Prop :=
  d.u ≠ none ∧
    d.v ≠ none ∧
    d.w ≠ none ∧
    d.u ≠ d.v ∧
    d.u ≠ d.w ∧
    d.v ≠ d.w ∧
    (∀ x y : P, d.alpha x = d.alpha y → x = y) ∧
    (∀ x : P, d.alpha x ≠ d.u) ∧
    (∀ z : Option B, z ≠ d.u → ∃ x : P, d.alpha x = z) ∧
    (∀ x y : P,
      Pgraph.Adj x y ↔
        (apexMaskExtension F S).Adj (d.alpha x) (d.alpha y)) ∧
    (∀ x y : K, d.beta x = d.beta y → x = y) ∧
    (∀ x : K, d.beta x ≠ d.v ∧ d.beta x ≠ d.w) ∧
    (∀ z : Option B,
      z ≠ d.v → z ≠ d.w → ∃ x : K, d.beta x = z) ∧
    (∀ x y : K,
      Kgraph.Adj x y ↔
        (apexMaskExtension F S).Adj (d.beta x) (d.beta y))

/-- The root-to-apex extension operation. -/
def extendComplete
    {B P K : Type*}
    (F : SimpleGraph B) (Pgraph : SimpleGraph P) (Kgraph : SimpleGraph K)
    (S : Set B)
    (c : CompleteIncidenceData F Pgraph Kgraph S) :
    MarkedTransverseData F Pgraph Kgraph S :=
  { u := some c.u
    v := some c.v
    w := some c.w
    alpha := c.phi
    beta := c.psi }

abbrev CompleteCarrier
    {B P K : Type*} [DecidableEq B] [DecidableEq P] [DecidableEq K]
    (F : SimpleGraph B) (Pgraph : SimpleGraph P) (Kgraph : SimpleGraph K)
    (S : Set B) :=
  {c : CompleteIncidenceData F Pgraph Kgraph S //
    completeIncidenceValid F Pgraph Kgraph S c}

abbrev MarkedCarrier
    {B P K : Type*} [Fintype B] [DecidableEq B] [DecidableEq P] [DecidableEq K]
    (F : SimpleGraph B) (Pgraph : SimpleGraph P) (Kgraph : SimpleGraph K)
    (S : Set B) :=
  {d : MarkedTransverseData F Pgraph Kgraph S //
    markedTransverseValid F Pgraph Kgraph S d}

/-- Claim 29491: at each mask, the explicit root-to-apex extension and its
root-preimage restriction give a bijection of the full map-bearing certificate
carriers. -/
def claim29491_maskwiseMultiplicityPreservingBijection : Prop :=
  ∀ (m : ℕ)
    {B P K : Type*}
    [Fintype B] [DecidableEq B]
    [Fintype P] [DecidableEq P]
    [Fintype K] [DecidableEq K],
    Fintype.card B = m →
      Fintype.card P = m →
        Fintype.card K = m - 1 →
          ∀ (F : SimpleGraph B) (Pgraph : SimpleGraph P)
            (Kgraph : SimpleGraph K) (S : Set B),
            ∃ (extend :
                CompleteCarrier F Pgraph Kgraph S →
                  MarkedCarrier F Pgraph Kgraph S)
              (restrict :
                MarkedCarrier F Pgraph Kgraph S →
                  CompleteCarrier F Pgraph Kgraph S),
              (∀ c : CompleteCarrier F Pgraph Kgraph S,
                (extend c).1 = extendComplete F Pgraph Kgraph S c.1) ∧
                (∀ c : CompleteCarrier F Pgraph Kgraph S,
                  (extend c).1.u = some c.1.u ∧
                    (extend c).1.v = some c.1.v ∧
                    (extend c).1.w = some c.1.w ∧
                    (extend c).1.alpha c.1.p = none ∧
                    (extend c).1.beta c.1.k = none) ∧
                (∀ d : MarkedCarrier F Pgraph Kgraph S,
                  some (restrict d).1.u = d.1.u ∧
                    some (restrict d).1.v = d.1.v ∧
                    some (restrict d).1.w = d.1.w ∧
                    d.1.alpha (restrict d).1.p = none ∧
                    d.1.beta (restrict d).1.k = none ∧
                    (∀ x : P,
                      d.1.alpha x = none → x = (restrict d).1.p) ∧
                    (∀ x : K,
                      d.1.beta x = none → x = (restrict d).1.k) ∧
                    (∀ x : P, x ≠ (restrict d).1.p →
                      (restrict d).1.phi x = d.1.alpha x) ∧
                    (∀ x : K, x ≠ (restrict d).1.k →
                      (restrict d).1.psi x = d.1.beta x)) ∧
                Function.Bijective extend ∧
                (∀ c : CompleteCarrier F Pgraph Kgraph S,
                  restrict (extend c) = c) ∧
                (∀ d : MarkedCarrier F Pgraph Kgraph S,
                  extend (restrict d) = d)

end MathlibPlus.Open.ResearchFormalization.R0667Claim29491
