import Mathlib

namespace MathlibPlus.Open.GraphTheory

open scoped BigOperators

private abbrev R21G := (Fin 3 → ZMod 2) × ZMod 9
private abbrev R21V := Fin 3 → ZMod 2
private abbrev R21H := ZMod 9

private abbrev R21Connection (k : ℕ) :=
  {S : Finset R21G //
    S.card = k ∧ (0 : R21G) ∉ S ∧ ∀ x ∈ S, -x ∈ S}

private noncomputable def r21Adj (S : Finset R21G) (x y : R21G) : Prop :=
  x ≠ y ∧ y - x ∈ S

private noncomputable def r21GraphIso (S T : Finset R21G) : Prop :=
  ∃ e : Equiv.Perm R21G, ∀ x y,
    r21Adj S x y ↔ r21Adj T (e x) (e y)

private noncomputable def r21GraphAut (S : Finset R21G) (e : Equiv.Perm R21G) : Prop :=
  ∀ x y, r21Adj S x y ↔ r21Adj S (e x) (e y)

private noncomputable def r21PresentationOrbit (S T : Finset R21G) : Prop :=
  ∃ e : R21G ≃+ R21G, T = S.image e

private noncomputable def r21CI (S : R21Connection 21) : Prop :=
  ∀ T : R21Connection 21, r21GraphIso S.1 T.1 →
    ∃ e : R21G ≃+ R21G, T.1 = S.1.image e

private noncomputable def r21Complement (S : R21Connection 21) : Finset R21G :=
  (Finset.univ : Finset R21G).erase 0 \ S.1

private noncomputable def r21Connected (S : R21Connection 21) : Prop :=
  AddSubgroup.closure (S.1 : Set R21G) = ⊤

private noncomputable def r21GeneratedOrder (S : R21Connection 21) : ℕ :=
  Nat.card (AddSubgroup.closure (S.1 : Set R21G))

private noncomputable def r21SingletonCount (S : R21Connection 21) : ℕ :=
  Nat.card {x : R21G // x ∈ S.1 ∧ x ≠ 0 ∧ -x = x}

private abbrev R21Atom :=
  {A : Finset R21G // ∃ x : R21G, x ≠ 0 ∧ A = {x, -x}}

private noncomputable def r21InducedAction (H : Subgroup (Equiv.Perm R21Atom)) : Prop :=
  (∀ p : Equiv.Perm R21Atom, p ∈ H ↔
    ∃ e : R21G ≃+ R21G, ∀ A : R21Atom,
      (p A).1 = A.1.image e) ∧
  (∀ e : R21G ≃+ R21G, ∃ p : H, ∀ A : R21Atom,
      (p.1 A).1 = A.1.image e)

private noncomputable def r21AtomOrbit
    (H : Subgroup (Equiv.Perm R21Atom))
    (S T : R21Connection 21) : Prop :=
  ∃ p : H, ∃ e : R21G ≃+ R21G,
    (∀ A : R21Atom, (p.1 A).1 = A.1.image e) ∧
    T.1 = S.1.image e

private noncomputable def r21AtomOrbitTypes
    (H : Subgroup (Equiv.Perm R21Atom)) (n s : ℕ) : Prop :=
  ∃ reps : Finset (R21Connection 21),
    reps.card = n ∧
    (∀ R ∈ reps, r21SingletonCount R = s) ∧
    (∀ S : R21Connection 21, r21SingletonCount S = s →
      ∃! R : R21Connection 21, R ∈ reps ∧ r21AtomOrbit H S R)

private noncomputable def r21AllGraphTypes : Prop :=
  ∃ reps : Finset (R21Connection 21),
    reps.card = 3452426 ∧
    ∀ S : R21Connection 21,
      ∃! R : R21Connection 21, R ∈ reps ∧ r21GraphIso S.1 R.1

private noncomputable def r21ConnectedGraphTypes : Prop :=
  ∃ reps : Finset (R21Connection 21),
    reps.card = 3450253 ∧
    (∀ R ∈ reps, r21Connected R) ∧
    ∀ S : R21Connection 21, r21Connected S →
      ∃! R : R21Connection 21, R ∈ reps ∧ r21GraphIso S.1 R.1

private noncomputable def r21OrderGraphTypes (n count : ℕ) : Prop :=
  ∃ reps : Finset (R21Connection 21),
    reps.card = count ∧
    (∀ R ∈ reps, r21GeneratedOrder R = n) ∧
    ∀ S : R21Connection 21, r21GeneratedOrder S = n →
      ∃! R : R21Connection 21, R ∈ reps ∧ r21GraphIso S.1 R.1

private noncomputable def r21PreservingPartition :
    R21Connection 21 → Prop := fun S =>
  ∀ e : Equiv.Perm R21G, r21GraphAut S.1 e →
    ∀ B ∈ (Finset.univ : Finset R21H).image (fun h =>
      (Finset.univ : Finset R21V).image (fun v => (v, h))),
      ∃ C ∈ (Finset.univ : Finset R21H).image (fun h =>
        (Finset.univ : Finset R21V).image (fun v => (v, h))),
        B.image e = C

private noncomputable def r21PartitionBreaking (S : R21Connection 21) : Prop :=
  ¬ r21PreservingPartition S

private noncomputable def r21BaseAction (S : R21Connection 21) : Set (Equiv.Perm R21H) :=
  {σ | ∃ e : Equiv.Perm R21G,
    r21GraphAut S.1 e ∧ e (0, 0) = (0, 0) ∧
    r21PreservingPartition S ∧
    ∀ v : R21V, ∀ h : R21H, (e (v, h)).2 = σ h}

private noncomputable def r21IdentityStabilizer (S : R21Connection 21) : Set (Equiv.Perm R21G) :=
  {e | r21GraphAut S.1 e ∧ e (0, 0) = (0, 0)}

private noncomputable def r21NonlinearBase (S : R21Connection 21) : Prop :=
  ∃ σ : Equiv.Perm R21H, σ ∈ r21BaseAction S ∧
    ¬ ∃ e : R21H ≃+ R21H, ∀ h, e h = σ h

private noncomputable def r21PartitionTypeRepresentatives : Prop :=
  ∃ reps : Finset (R21Connection 21),
    reps.card = 3427698 ∧
    (∀ R ∈ reps, r21PreservingPartition R) ∧
    ∀ S : R21Connection 21, r21PreservingPartition S →
      ∃! R : R21Connection 21, R ∈ reps ∧ r21GraphIso S.1 R.1

private noncomputable def r21BreakingTypeRepresentatives : Prop :=
  ∃ reps : Finset (R21Connection 21),
    reps.card = 24728 ∧
    (∀ R ∈ reps, r21PartitionBreaking R) ∧
    ∀ S : R21Connection 21, r21PartitionBreaking S →
      ∃! R : R21Connection 21, R ∈ reps ∧ r21GraphIso S.1 R.1

private noncomputable def r21ConnectedBreakingTypeRepresentatives : Prop :=
  ∃ reps : Finset (R21Connection 21),
    reps.card = 22555 ∧
    (∀ R ∈ reps, r21PartitionBreaking R ∧ r21Connected R) ∧
    ∀ S : R21Connection 21, r21PartitionBreaking S → r21Connected S →
      ∃! R : R21Connection 21, R ∈ reps ∧ r21GraphIso S.1 R.1

private noncomputable def r21NonlinearTypeRepresentatives : Prop :=
  ∃ reps : Finset (R21Connection 21),
    reps.card = 643 ∧
    (∀ R ∈ reps, r21PreservingPartition R ∧ r21NonlinearBase R ∧
      r21Connected R ∧ r21CI R) ∧
    ∀ S : R21Connection 21,
      r21PreservingPartition S → r21NonlinearBase S →
      ∃! R : R21Connection 21, R ∈ reps ∧ r21GraphIso S.1 R.1

private noncomputable def r21NonlinearOrderTypeRepresentatives
    (n m count : ℕ) : Prop :=
  ∃ reps : Finset (R21Connection 21),
    reps.card = count ∧
    (∀ R ∈ reps, r21NonlinearBase R ∧
      Nat.card {σ : Equiv.Perm R21H // σ ∈ r21BaseAction R} = n ∧
      Nat.card {e : Equiv.Perm R21G // e ∈ r21IdentityStabilizer R} = m) ∧
    ∀ S : R21Connection 21, r21NonlinearBase S →
      Nat.card {σ : Equiv.Perm R21H // σ ∈ r21BaseAction S} = n →
      Nat.card {e : Equiv.Perm R21G // e ∈ r21IdentityStabilizer S} = m →
      ∃! R : R21Connection 21, R ∈ reps ∧ r21GraphIso S.1 R.1

private noncomputable def r21RegularCopy (S : Finset R21G)
    (K : Subgroup (Equiv.Perm R21G)) : Prop :=
  (∀ g : Equiv.Perm R21G, g ∈ K → r21GraphAut S g) ∧
  Nonempty (K ≃* Multiplicative R21G) ∧
  ∀ x y : R21G, ∃! g : K, g.1 x = y

private noncomputable def r21ConjugateCopies (S : Finset R21G)
    (K L : Subgroup (Equiv.Perm R21G)) : Prop :=
  ∃ e : Equiv.Perm R21G, r21GraphAut S e ∧
    (∀ k : Equiv.Perm R21G, k ∈ K →
      ∃ l : Equiv.Perm R21G, l ∈ L ∧ e * k * e⁻¹ = l) ∧
    (∀ l : Equiv.Perm R21G, l ∈ L →
      ∃ k : Equiv.Perm R21G, k ∈ K ∧ e⁻¹ * l * e = k)

/-- The valency-21 connection sets have the four stated singleton-atom
    layers on the concrete group `C₂³ × C₉`. -/
def valency21ConnectionSetLayers_claim33244 : Prop :=
  Nat.card (R21Connection 21) = 1657543836 ∧
  (∀ S : R21Connection 21,
    r21SingletonCount S = 1 ∨ r21SingletonCount S = 3 ∨
      r21SingletonCount S = 5 ∨ r21SingletonCount S = 7) ∧
  Nat.card {S : R21Connection 21 // r21SingletonCount S = 1} = 451585680 ∧
  Nat.card {S : R21Connection 21 // r21SingletonCount S = 3} = 981708000 ∧
  Nat.card {S : R21Connection 21 // r21SingletonCount S = 5} = 220884300 ∧
  Nat.card {S : R21Connection 21 // r21SingletonCount S = 7} = 3365856

/-- The order-504 action is the induced faithful permutation group on the
    explicit inverse-atom carrier, and its orbit and Burnside data are stated
    without replacing the action by detached arithmetic. -/
def valency21PresentationOrbitQuotient_claim33245 : Prop :=
  ∃ H : Subgroup (Equiv.Perm R21Atom),
    letI : Fintype H := Fintype.ofFinite H
    Nat.card H = 504 ∧ r21InducedAction H ∧
    ∃ reps : Finset (R21Connection 21),
      reps.card = 3452426 ∧
      (∀ S : R21Connection 21,
        ∃! R : R21Connection 21, R ∈ reps ∧ r21AtomOrbit H S R) ∧
    r21AtomOrbitTypes H 952358 1 ∧
    r21AtomOrbitTypes H 2023976 3 ∧
    r21AtomOrbitTypes H 466590 5 ∧
    r21AtomOrbitTypes H 9502 7 ∧
    ∑ p : H, Nat.card {S : R21Connection 21 //
      ∃ e : R21G ≃+ R21G,
        (∀ A : R21Atom, (p.1 A).1 = A.1.image e) ∧
        S.1.image e = S.1} = 1740022704

/-- On valency-21 connection sets, ordinary graph-isomorphism fibers and
    additive-automorphism presentation orbits coincide. -/
def valency21GraphIsomorphismEqualsPresentationOrbit_claim33246 : Prop :=
  r21AllGraphTypes ∧
  ∀ S T : R21Connection 21,
    r21GraphIso S.1 T.1 ↔ r21PresentationOrbit S.1 T.1

/-- Every inverse-closed identity-free valency-21 Cayley graph on the concrete
    group is CI. -/
def valency21CayleyCI_claim33247 : Prop :=
  ∀ S : R21Connection 21, r21CI S

/-- Complementation inside the 71 nonidentity elements is explicit, preserves
    both graph-isomorphism and presentation fibers, and gives CI at valency 50. -/
def complementaryValency50CI_claim33248 : Prop :=
  (∀ S : R21Connection 21,
    (r21Complement S).card = 50 ∧
    (∀ x, x ∈ r21Complement S ↔ -x ∈ r21Complement S) ∧
    (0 : R21G) ∉ r21Complement S) ∧
  (∀ S T : R21Connection 21,
    (r21GraphIso S.1 T.1 ↔
      r21GraphIso (r21Complement S) (r21Complement T)) ∧
    (r21PresentationOrbit S.1 T.1 ↔
      r21PresentationOrbit (r21Complement S) (r21Complement T))) ∧
  (∀ S : R21Connection 21,
    ∀ T : R21Connection 50,
      r21GraphIso (r21Complement S) T.1 →
        ∃ e : R21G ≃+ R21G, T.1 = (r21Complement S).image e)

/-- Babai's regular-subgroup consequence is retained for both complementary
    valencies, with the full graph automorphism condition written out. -/
def valency21BabaiRegularSubgroups_claim33249 : Prop :=
  (∀ S : R21Connection 21,
    ∀ K L : Subgroup (Equiv.Perm R21G),
      r21RegularCopy S.1 K → r21RegularCopy S.1 L →
      r21ConjugateCopies S.1 K L) ∧
  (∀ S : R21Connection 21,
    ∀ K L : Subgroup (Equiv.Perm R21G),
      r21RegularCopy (r21Complement S) K →
      r21RegularCopy (r21Complement S) L →
      r21ConjugateCopies (r21Complement S) K L)

/-- The connected graph-type census retains the three generated-subgroup
    orders as graph-type counts rather than labelled-set counts. -/
def valency21ConnectedGraphTypeCensus_claim33250 : Prop :=
  r21AllGraphTypes ∧ r21ConnectedGraphTypes ∧
  r21OrderGraphTypes 24 3 ∧
  r21OrderGraphTypes 36 2170 ∧
  r21OrderGraphTypes 72 3450253

/-- The natural binary-fiber partition exception census is stated on ordinary
    graph-type representatives and keeps the connected and CI clauses. -/
def valency21NaturalPartitionExceptions_claim33251 : Prop :=
  r21PartitionTypeRepresentatives ∧
  r21BreakingTypeRepresentatives ∧
  r21ConnectedBreakingTypeRepresentatives ∧
  (∀ S : R21Connection 21, r21PartitionBreaking S → r21CI S)

/-- The nonlinear base-action census uses the actual induced permutation action
    on the nine quotient blocks and the identity stabilizer of the graph. -/
def valency21NonlinearBaseActionExceptions_claim33252 : Prop :=
  r21NonlinearTypeRepresentatives ∧
  r21NonlinearOrderTypeRepresentatives 1296 144 635 ∧
  r21NonlinearOrderTypeRepresentatives 362880 40320 8 ∧
  (∀ S : R21Connection 21,
    r21NonlinearBase S → r21Connected S ∧ r21CI S)

/-- The two ambient exception families are disjoint and all their members,
    together with their complementary graphs, remain CI. -/
def valency21AggregateAmbientExceptions_claim33253 : Prop :=
  r21BreakingTypeRepresentatives ∧ r21NonlinearTypeRepresentatives ∧
  (∀ S : R21Connection 21, r21PartitionBreaking S → ¬ r21NonlinearBase S) ∧
  24728 + 643 = (25371 : ℕ) ∧
  (∀ S : R21Connection 21,
    (r21PartitionBreaking S ∨ r21NonlinearBase S) →
      r21CI S ∧
      ∀ T : R21Connection 50,
        r21GraphIso (r21Complement S) T.1 →
          ∃ e : R21G ≃+ R21G, T.1 = (r21Complement S).image e)

end MathlibPlus.Open.GraphTheory
