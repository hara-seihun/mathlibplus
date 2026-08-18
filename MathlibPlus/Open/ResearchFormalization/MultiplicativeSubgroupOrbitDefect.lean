import MathlibPlus.GroupTheory.Claim14536

namespace MathlibPlus.Open.ResearchFormalization.MultiplicativeSubgroupOrbitDefect

open scoped BigOperators

noncomputable section

abbrev PrimeField (p : ℕ) := ZMod p
abbrev CayleyPower (p r : ℕ) := Multiplicative (Fin r → PrimeField p)

/-- The value in `F_p` of an element of a subgroup of the unit group. -/
def unitValue {p : ℕ} {H : Subgroup (PrimeField p)ˣ} (u : H) : PrimeField p :=
  (u.1 : PrimeField p)

/-- The value in `F_p` of an ambient unit. -/
def ambientUnitValue {p : ℕ} (u : (PrimeField p)ˣ) : PrimeField p :=
  (u : PrimeField p)

/-- The three moment characters used in the admissibility condition. -/
def momentCharacterOne {p : ℕ} (H : Subgroup (PrimeField p)ˣ) :
    H → (PrimeField p)ˣ :=
  fun _ => 1

def momentCharacterIdentity {p : ℕ} (H : Subgroup (PrimeField p)ˣ) :
    H → (PrimeField p)ˣ :=
  fun h => h.1

def momentCharacterCubic {p : ℕ} (H : Subgroup (PrimeField p)ˣ) :
    H → (PrimeField p)ˣ :=
  fun h => h.1 ^ 3

/-- Pairwise distinctness of the characters `1`, `h`, and `h^3` on `H`. -/
def distinctMomentCharacters {p : ℕ} (H : Subgroup (PrimeField p)ˣ) : Prop :=
  momentCharacterOne H ≠ momentCharacterIdentity H ∧
    momentCharacterOne H ≠ momentCharacterCubic H ∧
      momentCharacterIdentity H ≠ momentCharacterCubic H

/-- The complete homogeneous polynomial `h_n(a,b,c)`. -/
def completeHomogeneous (p n : ℕ)
    (a b c : PrimeField p) : PrimeField p :=
  ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ Finset.range (n + 1 - i),
      a ^ i * b ^ j * c ^ (n - i - j)

/-- The elementary symmetric coefficient `s_2`. -/
def secondElementary (a b c : PrimeField p) : PrimeField p :=
  a * b + a * c + b * c

/-- The elementary symmetric coefficient `s_3`. -/
def thirdElementary (a b c : PrimeField p) : PrimeField p :=
  a * b * c

/-- The signed Vandermonde factor used by the slope formula. -/
def signedVandermonde (a b c : PrimeField p) : PrimeField p :=
  (a - b) * (b - c) * (c - a)

/-- The coefficient-integrated slope from the admitted multiplicative-subgroup
orbit theorem.  The inverse is the field inverse when `p` is prime. -/
def cubicSlope (p : ℕ) (a b c : PrimeField p) : PrimeField p :=
  -signedVandermonde a b c *
    ∑ k ∈ Finset.Icc 2 (p - 1),
      secondElementary a b c ^ k *
        thirdElementary a b c ^ (p - k) *
          completeHomogeneous p (k - 2) a b c *
            (k : PrimeField p)⁻¹

/-- A subgroup is admissible exactly when the three moment characters are
 distinct and it contains the stated distinct zero-sum triple with nonzero
 coefficient-integrated slope. -/
def admissibleSubgroup (p : ℕ) (H : Subgroup (PrimeField p)ˣ) : Prop :=
  distinctMomentCharacters H ∧
    ∃ a b c : H,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        unitValue a + unitValue b + unitValue c = 0 ∧
          cubicSlope p (unitValue a) (unitValue b) (unitValue c) ≠ 0

/-- The set of all subgroup orders allowed by the literal definition of `d(p)`. -/
def admissibleOrders (p : ℕ) : Set ℕ :=
  {d | ∃ H : Subgroup (PrimeField p)ˣ,
    admissibleSubgroup p H ∧ Nat.card H = d}

/-- The literal minimum of the admissible subgroup orders.  The theorem below
includes attainment and the lower-bound property, so the empty-set default of
` sInf` is never used in its asserted range. -/
noncomputable def admissibleMinimum (p : ℕ) : ℕ :=
  sInf (admissibleOrders p)

def literalAdmissibleMinimum (p d : ℕ) : Prop :=
  (∃ H : Subgroup (PrimeField p)ˣ,
      admissibleSubgroup p H ∧ Nat.card H = d) ∧
    ∀ e : ℕ,
      (∃ H : Subgroup (PrimeField p)ˣ,
        admissibleSubgroup p H ∧ Nat.card H = e) → d ≤ e

/-- Identity-free inverse-closed subsets in an additive model of an
 elementary abelian group. -/
def additiveConnectionSet {V : Type*} [AddGroup V] (S : Set V) : Prop :=
  (0 : V) ∉ S ∧
    ∀ ⦃x : V⦄, x ∈ S → -x ∈ S

/-- Ordinary undirected Cayley-graph isomorphism in additive notation. -/
def additiveCayleyGraphIsomorphic {V : Type*} [AddCommGroup V]
    (S T : Set V) : Prop :=
  ∃ e : V ≃ V, ∀ x y : V,
    (x ≠ y ∧ y - x ∈ S) ↔
      (e x ≠ e y ∧ e y - e x ∈ T)

/-- Connectedness of an additive Cayley connection set. -/
def additiveCayleyConnected {V : Type*} [AddGroup V] (S : Set V) : Prop :=
  AddSubgroup.closure S = ⊤

/-- An explicit connected, identity-free, inverse-closed Cayley defect. -/
def additiveCayleyWitness {V : Type*} [AddCommGroup V]
    (S T : Set V) : Prop :=
  additiveConnectionSet S ∧
    additiveConnectionSet T ∧
      additiveCayleyConnected S ∧
        additiveCayleyConnected T ∧
          additiveCayleyGraphIsomorphic S T ∧
            ¬ ∃ e : V ≃+ V, Set.image e S = T

/-- The moment functional `mu_j(q)=sum t^j q_t`. -/
def momentFunctional (p j : ℕ)
    (H : Subgroup (PrimeField p)ˣ) :
    (H → PrimeField p) →ₗ[PrimeField p] PrimeField p :=
  ((Set.toFinite (Set.univ : Set H)).toFinset).sum
    (fun t => (ambientUnitValue t.1 ^ j) • LinearMap.proj t)

/-- The common kernel `Q=ker(mu_0) intersect ker(mu_1) intersect ker(mu_3)`. -/
def momentKernel (p : ℕ) (H : Subgroup (PrimeField p)ˣ) :
    Submodule (PrimeField p) (H → PrimeField p) :=
  (momentFunctional p 0 H).ker ⊓
    (momentFunctional p 1 H).ker ⊓
      (momentFunctional p 3 H).ker

/-- The dual space `A=Q*` in the construction. -/
abbrev DualMomentSpace (p : ℕ) (H : Subgroup (PrimeField p)ˣ) :=
  Module.Dual (PrimeField p) (momentKernel p H)

abbrev CubicBaseSpace (p : ℕ) := Fin 3 → PrimeField p

/-- The covector `c_u` supported on the three entries of an oriented triple. -/
def triangleCovector {p : ℕ} {H : Subgroup (PrimeField p)ˣ}
    (u1 u2 u3 : H) : H → PrimeField p :=
  fun t =>
    if t = u1 then unitValue u2 - unitValue u3
    else if t = u2 then unitValue u3 - unitValue u1
    else if t = u3 then unitValue u1 - unitValue u2
    else 0

/-- The direction `d_u=(1,s_2(u),s_3(u))` in the cubic base. -/
def orbitDirection {p : ℕ} {H : Subgroup (PrimeField p)ˣ}
    (x y h : H) : CubicBaseSpace p :=
  ![1,
    secondElementary (unitValue h) (unitValue (h * x)) (unitValue (h * y)),
    thirdElementary (unitValue h) (unitValue (h * x)) (unitValue (h * y))]

/-- The slope `lambda_u` attached to the same oriented triple. -/
def orbitSlope (p : ℕ) {H : Subgroup (PrimeField p)ˣ}
    (x y h : H) : PrimeField p :=
  cubicSlope p (unitValue h) (unitValue (h * x)) (unitValue (h * y))

/-- The eight unsigned marker directions in `B`. -/
def markerSeedSet (p : ℕ) : Set (CubicBaseSpace p) :=
  { ![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0],
    ![1, 2, 0], ![1, 0, 1], ![1, 0, 3], ![1, 1, 1] }

/-- The signed marker `M=+-2{...}`. -/
def signedMarker (p : ℕ) : Set (CubicBaseSpace p) :=
  Set.image (fun v => (2 : PrimeField p) • v) (markerSeedSet p) ∪
    Set.image (fun v => -((2 : PrimeField p) • v)) (markerSeedSet p)

/-- Full `A`-fibres over the signed marker. -/
def markerFibres {p : ℕ} (A : Type*)
    (M : Set (CubicBaseSpace p)) : Set (A × CubicBaseSpace p) :=
  {q | q.2 ∈ M}

/-- Negation of a set, used for the inverse-paired rows. -/
def negativeSet {V : Type*} [Neg V] (S : Set V) : Set V :=
  {x | -x ∈ S}

/-- The retained row family over the multiplicative orbit. -/
def orbitRowSet {p : ℕ} {H : Subgroup (PrimeField p)ˣ}
    (x y : H) (c : ∀ h : H, momentKernel p H)
    (q : H → PrimeField p) :
    Set (DualMomentSpace p H × CubicBaseSpace p) :=
  {v | ∃ h : H,
    v.2 = orbitDirection x y h ∧ v.1 (c h) = q h}

/-- The concrete orbit-and-marker construction from the admitted proof.  The
existential data are tied to the displayed moment kernels, covectors, rows,
slopes, and shear rather than being arbitrary graph certificates. -/
def explicitOrbitConstruction {p : ℕ} [Fact p.Prime]
    (H : Subgroup (PrimeField p)ˣ) (x y : H)
    (c : ∀ h : H, momentKernel p H)
    (s : CubicBaseSpace p → DualMomentSpace p H) : Prop :=
  let rowZero := orbitRowSet x y c (fun _ => 0)
  let rowSlope := orbitRowSet x y c (orbitSlope p x y)
  let S0 := rowZero ∪ negativeSet rowZero ∪
    markerFibres (DualMomentSpace p H) (signedMarker p)
  let S1 := rowSlope ∪ negativeSet rowSlope ∪
    markerFibres (DualMomentSpace p H) (signedMarker p)
  (x ≠ (1 : H) ∧ y ≠ (1 : H) ∧ x ≠ y) ∧
    unitValue (1 : H) + unitValue x + unitValue y = 0 ∧
    orbitSlope p x y (1 : H) ≠ 0 ∧
    (∀ h : H, (c h).1 = triangleCovector (h : H) (h * x) (h * y)) ∧
    (∀ h : H, ∀ z : CubicBaseSpace p,
      (s (z + orbitDirection x y h) - s z) (c h) =
        orbitSlope p x y h) ∧
    (∀ z : CubicBaseSpace p, s (-z) = -s z) ∧
    (∀ h k : H, orbitDirection x y h = orbitDirection x y k → h = k) ∧
    (∀ h : H,
      orbitSlope p x y h =
        ambientUnitValue h.1 ^ 4 * orbitSlope p x y (1 : H)) ∧
    Module.finrank (PrimeField p) (DualMomentSpace p H) = Nat.card H - 3 ∧
    Module.finrank (PrimeField p)
        (DualMomentSpace p H × CubicBaseSpace p) = Nat.card H ∧
    Nonempty ((DualMomentSpace p H × CubicBaseSpace p) ≃+
      (Fin (Nat.card H) → PrimeField p)) ∧
    AddSubgroup.closure
        (markerFibres (DualMomentSpace p H) (signedMarker p)) = ⊤ ∧
    additiveCayleyWitness S0 S1 ∧
    (∃ e : (DualMomentSpace p H × CubicBaseSpace p) ≃
        (DualMomentSpace p H × CubicBaseSpace p),
      (∀ q, e q = (q.1 + s q.2, q.2)) ∧
      (∀ u v : DualMomentSpace p H × CubicBaseSpace p,
        (u ≠ v ∧ v - u ∈ S0) ↔
          (e u ≠ e v ∧ e v - e u ∈ S1)))

/-- The rank-`d` witness is the displayed construction for an admissible
subgroup of order `d`. -/
def minimumOrbitWitness {p : ℕ} [Fact p.Prime] (d : ℕ) : Prop :=
  ∃ H : Subgroup (PrimeField p)ˣ,
    admissibleSubgroup p H ∧ Nat.card H = d ∧
      ∃ x y : H,
        ∃ c : ∀ h : H, momentKernel p H,
          ∃ s : CubicBaseSpace p → DualMomentSpace p H,
            explicitOrbitConstruction H x y c s

/-- The baseline threshold used by the deterministic certificate. -/
def admittedBaseline (p : ℕ) : ℕ :=
  if p = 11 then 10 else
    let deleted := (2 * p + 9) / 3
    if 23 ≤ p ∧ p ≤ 4999 then min deleted ((p - 1) / 2) else deleted

def rankGain (p : ℕ) : ℕ :=
  admittedBaseline p - admissibleMinimum p

def primeWindow : Finset ℕ :=
  (Finset.Icc 11 4999).filter Nat.Prime

def improvedPrimeWindow : Finset ℕ :=
  primeWindow.filter (fun p => admissibleMinimum p < admittedBaseline p)

/-- The exact p=53 subgroup-and-triple row named in the certificate. -/
def prime53Example : Prop :=
  ∃ H : Subgroup (PrimeField 53)ˣ,
    ∃ u : (PrimeField 53)ˣ,
      ambientUnitValue u = 16 ∧
        H = Subgroup.zpowers u ∧ Nat.card H = 13 ∧
          admissibleSubgroup 53 H ∧
            ∃ a b c : H,
              unitValue a = 1 ∧ unitValue b = 10 ∧ unitValue c = 42 ∧
                a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
                  unitValue a + unitValue b + unitValue c = 0 ∧
                    cubicSlope 53 (unitValue a) (unitValue b) (unitValue c) = 23

/-- The exact finite certificate reported for all primes from 11 through
4999, including the two named extremal rows. -/
def deterministicPrimeCertificate : Prop :=
  primeWindow.card = 665 ∧
    improvedPrimeWindow.card = 575 ∧
      (∀ p ∈ primeWindow, 10 ≤ admissibleMinimum p) ∧
        (∃ p ∈ primeWindow, admissibleMinimum p = 10) ∧
          (∀ p ∈ primeWindow, rankGain p ≤ 2419) ∧
            (∃ p ∈ primeWindow, rankGain p = 2419) ∧
              (∀ p ∈ primeWindow, p < 53 →
                admissibleMinimum p ≥ admittedBaseline p) ∧
                53 ∈ primeWindow ∧
                  admissibleMinimum 53 = 13 ∧
                    admittedBaseline 53 = 26 ∧
                      rankGain 53 = 13 ∧
                        prime53Example ∧
                          4957 ∈ primeWindow ∧
                            admissibleMinimum 4957 = 59 ∧
                              admittedBaseline 4957 = 2478 ∧
                                rankGain 4957 = 2419

/-- Claim 61206: the admitted multiplicative-subgroup orbit defect theorem. -/
def multiplicativeSubgroupOrbitDefects_claim61206 : Prop :=
  deterministicPrimeCertificate ∧
    ∀ (p : ℕ) [Fact p.Prime], 11 ≤ p →
      literalAdmissibleMinimum p (admissibleMinimum p) ∧
        minimumOrbitWitness (p := p) (admissibleMinimum p) ∧
          (∀ r : ℕ, admissibleMinimum p ≤ r →
            ¬ MathlibPlus.GroupTheory.Claim14536.ordinaryUndirectedCIGroup
                (CayleyPower p r)) ∧
            (∀ (G : Type*) [Finite G] [Group G],
              (∃ K : Subgroup G,
                Nonempty (CayleyPower p (admissibleMinimum p) ≃* K)) →
                ¬ MathlibPlus.GroupTheory.Claim14536.ordinaryUndirectedCIGroup G)

end

end MathlibPlus.Open.ResearchFormalization.MultiplicativeSubgroupOrbitDefect
