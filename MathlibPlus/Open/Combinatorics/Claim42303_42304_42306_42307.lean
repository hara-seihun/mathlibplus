import Mathlib

namespace MathlibPlus.Open.Combinatorics

open scoped BigOperators

noncomputable section

open Classical

/-- The actual finite ground of a finite family of finite sets. -/
def r2671Ground {n : ℕ} (F : Finset (Finset (Fin n))) : Finset (Fin n) :=
  F.biUnion (fun A => A)

/-- Coordinate incidence in a finite family. -/
def r2671Frequency {n : ℕ} (F : Finset (Finset (Fin n))) (x : Fin n) : ℕ :=
  (F.filter (fun A => x ∈ A)).card

/-- Pairwise union closure of a finite distinct-set family. -/
def r2671UnionClosed {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ ⦃A B : Finset (Fin n)⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

/-- Strict nonabundance on the actual finite ground. -/
def r2671FranklCounterexample {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  2 ≤ F.card ∧
    r2671UnionClosed F ∧
    (∀ x ∈ r2671Ground F, 2 * r2671Frequency F x < F.card)

/-- Minimum family cardinality followed by minimum actual ground cardinality. -/
def r2671MinimumCounterexample {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  r2671FranklCounterexample F ∧
    (∀ (m : ℕ) (H : Finset (Finset (Fin m))),
      r2671FranklCounterexample H →
        F.card ≤ H.card ∧
          (F.card = H.card → (r2671Ground F).card ≤ (r2671Ground H).card))

/-- The slack and tight coordinates used by the minimum-counterexample normal form. -/
def r2671Slack {n : ℕ} (F : Finset (Finset (Fin n))) (x : Fin n) : ℕ :=
  F.card - 2 * r2671Frequency F x

def r2671TightSet {n : ℕ} (F : Finset (Finset (Fin n))) : Finset (Fin n) :=
  (r2671Ground F).filter (fun x => r2671Slack F x = 1)

/-- Members whose individual deletion preserves union closure. -/
def r2671RemovableMembers {n : ℕ}
    (F : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  F.filter (fun A => r2671UnionClosed (F.erase A))

/-- Tight trace of a member. -/
def r2671Trace {n : ℕ} (A T : Finset (Fin n)) : Finset (Fin n) :=
  A ∩ T

/-- The members of a core having one prescribed tight trace. -/
def r2671TraceCell {n : ℕ}
    (G : Finset (Finset (Fin n))) (T S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  G.filter (fun A => r2671Trace A T = S)

/-- The down, up, comparable, and incomparable regions of an absent root. -/
def r2671DownRegion {n : ℕ}
    (G : Finset (Finset (Fin n))) (R : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  G.filter (fun A => A ⊆ R)

def r2671UpRegion {n : ℕ}
    (G : Finset (Finset (Fin n))) (R : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  G.filter (fun A => R ⊆ A)

def r2671ComparableRegion {n : ℕ}
    (G : Finset (Finset (Fin n))) (R : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  r2671DownRegion G R ∪ r2671UpRegion G R

def r2671IncomparableRegion {n : ℕ}
    (G : Finset (Finset (Fin n))) (R : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  G \ r2671ComparableRegion G R

/-- A finite V-cell has exactly two incomparable lower members and their union. -/
def r2671UnionClosedCell {n : ℕ} (C : Finset (Finset (Fin n))) : Prop :=
  ∀ ⦃A B : Finset (Fin n)⦄, A ∈ C → B ∈ C → A ∪ B ∈ C

def r2671VCell {n : ℕ}
    (C : Finset (Finset (Fin n))) (A B : Finset (Fin n)) : Prop :=
  C.card = 3 ∧
    C = {A, B, A ∪ B} ∧
    A ≠ B ∧
    ¬ A ⊆ B ∧
    ¬ B ⊆ A ∧
    r2671UnionClosedCell C

def r2671VCellWithIntersection {n : ℕ}
    (C : Finset (Finset (Fin n))) (S : Finset (Fin n)) : Prop :=
  ∃ A B : Finset (Fin n), r2671VCell C A B ∧ A ∩ B = S

/-- A coordinate root is the union of all members omitting that coordinate. -/
def r2671PrincipalZeroRoot {n : ℕ}
    (G : Finset (Finset (Fin n))) (x : Fin n) : Finset (Fin n) :=
  (G.filter (fun A => x ∉ A)).biUnion (fun A => A)

/-- The signature by which the complement-coordinate core records a member. -/
def r2671Signature {n : ℕ}
    (G : Finset (Finset (Fin n))) (A : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  G.filter (fun R => ¬ A ⊆ R)

/-- Join-irreducibility in the reverse-inclusion complement lattice. -/
def r2671ComplementMember {n : ℕ}
    (X A : Finset (Fin n)) : Finset (Fin n) :=
  X \ A

def r2671ComplementFamily {n : ℕ}
    (X : Finset (Fin n)) (G : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  G.image (r2671ComplementMember X)

def r2671ReverseJoinIrreducible {n : ℕ}
    (X : Finset (Fin n)) (G : Finset (Finset (Fin n))) (J : Finset (Fin n)) : Prop :=
  J ∈ r2671ComplementFamily X G ∧
    J ≠ X ∧
    (∀ A B : Finset (Fin n),
      A ∈ r2671ComplementFamily X G →
        B ∈ r2671ComplementFamily X G →
          A ∩ B = J → A = J ∨ B = J)

/-- The minimum-ground lattice-core and separating normalization. -/
def r2671CoordinateCore {n : ℕ} (G : Finset (Finset (Fin n))) : Prop :=
  (∀ A B : Finset (Fin n), A ∈ G → B ∈ G →
    r2671Signature G A = r2671Signature G B → A = B) ∧
    (∀ J : Finset (Fin n),
      r2671ReverseJoinIrreducible (r2671Ground G) G J →
        ∃ x ∈ r2671Ground G,
          r2671ComplementMember (r2671Ground G) (r2671PrincipalZeroRoot G x) = J) ∧
    (∀ x y : Fin n, x ∈ r2671Ground G → y ∈ r2671Ground G →
      (G.filter (fun A => x ∈ A)) = (G.filter (fun A => y ∈ A)) → x = y)

/-- Complete removable-trace kernel equality, written pointwise on the actual ground. -/
def r2671CompleteRemovableTraceKernel {n : ℕ}
    (G : Finset (Finset (Fin n))) (T : Finset (Fin n)) (p : Fin n) : Prop :=
  ∀ x : Fin n,
    ((∀ A : Finset (Fin n),
      A ∈ r2671RemovableMembers G →
        r2671Trace A T = {p} → x ∈ A) ↔ x = p)

/-- The exact removable-generation and deletion part of the normalized core. -/
def r2671CoreRemovableLaws {n : ℕ}
    (G : Finset (Finset (Fin n))) (T : Finset (Fin n)) : Prop :=
  (∀ D : Finset (Finset (Fin n)),
    D.Nonempty → D ⊆ r2671RemovableMembers G →
      ∃ x ∈ r2671Ground G,
        r2671Slack G x + 2 * r2671Frequency D x ≤ D.card) ∧
  (∀ A ∈ G, ∃ D : Finset (Finset (Fin n)),
    D ⊆ r2671RemovableMembers G ∧ D.biUnion (fun B => B) = A) ∧
  (∀ A ∈ r2671RemovableMembers G,
    (r2671Trace A T).card ≤ 1) ∧
  T ⊆ (r2671RemovableMembers G).biUnion (fun A => r2671Trace A T) ∧
  (∀ p ∈ T, ∃ A ∈ r2671RemovableMembers G,
    r2671Trace A T = {p}) ∧
  (∀ S : Finset (Fin n), S ⊆ T →
    ∃ A ∈ G, r2671Trace A T = S) ∧
  (∀ A ∈ G, (r2671Trace A T).card = 2 →
    A ∉ r2671RemovableMembers G) ∧
  (∀ p ∈ T, ({p} : Finset (Fin n)) ∉ G)

/-- The exact trace-cell lower bounds, pair exclusion, and arithmetic bounds retained
in the one-root analysis. -/
def r2671TraceArithmeticLaws {n : ℕ}
    (G : Finset (Finset (Fin n))) (T : Finset (Fin n)) : Prop :=
  (r2671TraceCell G T ∅).card ≤ 18 ∧
  (∀ p ∈ T,
    (r2671TraceCell G T ∅).card +
      (r2671TraceCell G T {p}).card ≤ 21) ∧
  (∀ S : Finset (Fin n), S ⊆ T → S.card = 1 →
    3 ≤ (r2671TraceCell G T S).card) ∧
  (∀ S : Finset (Fin n), S ⊆ T → S.card = 2 →
    3 ≤ (r2671TraceCell G T S).card) ∧
  (∀ S : Finset (Fin n), S ⊆ T → S.card = 2 → S ∉ G)

/-- The retained one-root region and saturation laws used before the terminal
comparable-region conclusions. -/
def r2671OneRootRetainedLaws {n : ℕ}
    (G : Finset (Finset (Fin n))) (T R : Finset (Fin n)) (p : Fin n) : Prop :=
  R ⊆ r2671Ground G ∧
  R ≠ ({p} : Finset (Fin n)) ∧
  (∃ x : Fin n, x ∈ R ∧ x ∉ T) ∧
  (let D := r2671DownRegion G R
   let K := r2671UpRegion G R
   let Q := r2671IncomparableRegion G R
   (∀ A ∈ D, ∀ B ∈ D, A ∪ B ∈ D) ∧
     K = (G \ D).image (fun A => A ∪ R) ∧
     r2671UnionClosed K ∧
     r2671UnionClosedCell (D ∪ K) ∧
     K.card ≤ 23 ∧
     3 ≤ (Q.filter (fun A => p ∈ A)).card ∧
     (D.card > 1 → K.card + (D.card + 1) / 2 ≤ 23) ∧
     ((Q.filter (fun A => p ∈ A)).card ≤ 5 →
       ∀ A ∈ D, r2671Trace A T ≠ {p}))

/-- The two absent-root extension laws. -/
def r2671RootExtensionLaw {n : ℕ}
    (G : Finset (Finset (Fin n))) (root : Finset (Fin n)) : Prop :=
  root ∉ G ∧
    (∀ A ∈ G, A ∪ root ∈ G ∨ A ∪ root = root) ∧
    (∀ A ∈ G, ¬ A ⊆ root → A ∪ root ∈ G)

/-- The full normalized exact-three minimum-counterexample core. -/
def r2671NormalizedCore {n : ℕ}
    (G : Finset (Finset (Fin n))) (T : Finset (Fin n))
    (p₀ p₁ p₂ : Fin n) : Prop :=
  r2671MinimumCounterexample G ∧
  G.card = 53 ∧
  (∅ : Finset (Fin n)) ∈ G ∧
  r2671Ground G = (Finset.univ : Finset (Fin n)) ∧
  Odd G.card ∧
  r2671CoordinateCore G ∧
  T = {p₀, p₁, p₂} ∧
  p₀ ≠ p₁ ∧ p₀ ≠ p₂ ∧ p₁ ≠ p₂ ∧
  T.card = 3 ∧
  r2671TightSet G = T ∧
  r2671CoreRemovableLaws G T ∧
  r2671CompleteRemovableTraceKernel G T p₀ ∧
  r2671CompleteRemovableTraceKernel G T p₁ ∧
  r2671CompleteRemovableTraceKernel G T p₂ ∧
  r2671TraceArithmeticLaws G T

/-- The normalized 55-member, exact k=67 terminal extension carrier. -/
def normalizedExactK67TerminalSlice_claim4230 {n : ℕ}
    (F G : Finset (Finset (Fin n))) (T R₁ R₂ : Finset (Fin n))
    (p₀ p₁ p₂ : Fin n) : Prop :=
  r2671NormalizedCore G T p₀ p₁ p₂ ∧
  r2671FranklCounterexample F ∧
  F.card = 55 ∧
  G.card = 53 ∧
  F = insert R₁ (insert R₂ G) ∧
  r2671Ground F = (Finset.univ : Finset (Fin n)) ∧
  R₁ ≠ R₂ ∧
  R₁ ∩ T = {p₁} ∧
  R₂ ∩ T = {p₂} ∧
  R₁ ∪ R₂ ∈ G ∧
  r2671RootExtensionLaw G R₁ ∧
  r2671RootExtensionLaw G R₂ ∧
  r2671OneRootRetainedLaws G T R₁ p₁ ∧
  r2671OneRootRetainedLaws G T R₂ p₂

/-- The equality profile of one extremal comparable region. -/
def r2671ExtremalTraceProfile
    {n : ℕ} (G : Finset (Finset (Fin n))) (T R : Finset (Fin n)) : Prop :=
  let D := r2671DownRegion G R
  let K := r2671UpRegion G R
  D.card = 18 ∧
  K.card = 13 ∧
  D = r2671TraceCell G T ∅ ∧
  (r2671TraceCell G T ∅).card = 18 ∧
  (∀ S : Finset (Fin n), S ⊆ T → S.card = 1 →
    (r2671TraceCell G T S).card = 3 ∧
      r2671VCellWithIntersection (r2671TraceCell G T S) S) ∧
  (∀ S : Finset (Fin n), S ⊆ T → S.card = 2 →
    (r2671TraceCell G T S).card = 3 ∧
      r2671VCellWithIntersection (r2671TraceCell G T S) S) ∧
  (r2671TraceCell G T T).card = 17

/-- Claim 42303: both extension roots have the 31-member comparable-region cap. -/
def oneRootComparableRegionCap_claim42303 : Prop :=
  ∀ (n : ℕ) (F G : Finset (Finset (Fin n)))
    (T R₁ R₂ : Finset (Fin n)) (p₀ p₁ p₂ : Fin n),
    normalizedExactK67TerminalSlice_claim4230 F G T R₁ R₂ p₀ p₁ p₂ →
      (r2671ComparableRegion G R₁).card ≤ 31 ∧
        (r2671ComparableRegion G R₂).card ≤ 31

/-- Claim 42304: either extremal root has the complete equality profile. -/
def equalityProfileOneExtremalRoot_claim42304 : Prop :=
  ∀ (n : ℕ) (F G : Finset (Finset (Fin n)))
    (T R₁ R₂ : Finset (Fin n)) (p₀ p₁ p₂ : Fin n),
    normalizedExactK67TerminalSlice_claim4230 F G T R₁ R₂ p₀ p₁ p₂ →
      ((r2671ComparableRegion G R₁).card = 31 →
        r2671ExtremalTraceProfile G T R₁) ∧
      ((r2671ComparableRegion G R₂).card = 31 →
        r2671ExtremalTraceProfile G T R₂)

/-- Claim 42306: the two comparable regions cannot both be extremal, and their
smaller cardinality is at most 30. -/
def simultaneousExtremalityImpossible_claim42306 : Prop :=
  ∀ (n : ℕ) (F G : Finset (Finset (Fin n)))
    (T R₁ R₂ : Finset (Fin n)) (p₀ p₁ p₂ : Fin n),
    normalizedExactK67TerminalSlice_claim4230 F G T R₁ R₂ p₀ p₁ p₂ →
      (¬ ((r2671ComparableRegion G R₁).card = 31 ∧
          (r2671ComparableRegion G R₂).card = 31)) ∧
        min (r2671ComparableRegion G R₁).card
          (r2671ComparableRegion G R₂).card ≤ 30

/-- Claim 42307: an empty-trace second down-region is contained in the first
extremal down-region. -/
def emptyTraceSecondDownRegionNested_claim42307 : Prop :=
  ∀ (n : ℕ) (F G : Finset (Finset (Fin n)))
    (T R₁ R₂ : Finset (Fin n)) (p₀ p₁ p₂ : Fin n),
    normalizedExactK67TerminalSlice_claim4230 F G T R₁ R₂ p₀ p₁ p₂ →
      (r2671ComparableRegion G R₁).card = 31 →
      (∀ A ∈ r2671DownRegion G R₂,
        r2671Trace A T = ∅) →
      r2671DownRegion G R₂ ⊆ r2671DownRegion G R₁

end

end MathlibPlus.Open.Combinatorics
