import Mathlib

namespace MathlibPlus.Open.Research.CIGainElementaryPreimageGauge

noncomputable section

/-- The permutation predicate for an automorphism of a simple graph. -/
def preservesGraph {Ω : Type*} (Γ : SimpleGraph Ω) (σ : Equiv.Perm Ω) : Prop :=
  ∀ u v, Γ.Adj (σ u) (σ v) ↔ Γ.Adj u v

/-- A subgroup presented as the full automorphism group of `Γ`. -/
def isGraphAutomorphismGroup {Ω : Type*} (Γ : SimpleGraph Ω)
    (A : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ σ, σ ∈ A ↔ preservesGraph Γ σ

/-- The orbit of a point under a permutation subgroup. -/
def permutationOrbit {Ω : Type*} (D : Subgroup (Equiv.Perm Ω)) (ω : Ω) : Set Ω :=
  {v | ∃ d : D, (d : Equiv.Perm Ω) ω = v}

/-- The actual carrier consisting of the `D`-orbits. -/
def orbitBlocks {Ω : Type*} (D : Subgroup (Equiv.Perm Ω)) :=
  {B : Set Ω // ∃ ω : Ω, B = permutationOrbit D ω}

/-- A map from vertices to the actual orbit carrier. -/
def isOrbitMap {Ω : Type*} (D : Subgroup (Equiv.Perm Ω))
    (blockOf : Ω → orbitBlocks D) : Prop :=
  ∀ ω, (blockOf ω).1 = permutationOrbit D ω

/-- A chosen origin in every orbit, together with the orbit map. -/
def isOriginChoice {Ω : Type*} (D : Subgroup (Equiv.Perm Ω))
    (origin : orbitBlocks D → Ω) (blockOf : Ω → orbitBlocks D) : Prop :=
  (∀ B, origin B ∈ B.1) ∧
    (∀ B, blockOf (origin B) = B)

/-- The action on the orbit carrier induced by actual permutations of `Ω`. -/
def inducesOrbitAction {Ω : Type*} (D : Subgroup (Equiv.Perm Ω))
    (Y : Subgroup (Equiv.Perm Ω))
    (rho : Y →* Equiv.Perm (orbitBlocks D)) : Prop :=
  ∀ y : Y, ∀ B : orbitBlocks D,
    (rho y B).1 = (y : Equiv.Perm Ω) '' B.1

/-- The exact centralizer condition inside the graph automorphism group. -/
def isCentralizer {Ω : Type*} (A D Y : Subgroup (Equiv.Perm Ω)) : Prop :=
  Y ≤ A ∧
    ∀ a, a ∈ A →
      (a ∈ Y ↔ ∀ d, d ∈ D → a * d = d * a)

/-- Semiregularity for an actual permutation subgroup. -/
def isSemiregular {Ω : Type*} (D : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ d, d ∈ D → ∀ ω, d ω = ω → d = 1

/-- Regularity for an actual permutation subgroup on its carrier. -/
def isRegular {B : Type*} (Q : Subgroup (Equiv.Perm B)) : Prop :=
  (∀ x y : B, ∃ q : Q, (q : Equiv.Perm B) x = y) ∧
    (∀ q : Q, ∀ x : B, (q : Equiv.Perm B) x = x → q = 1)

/-- Elementary abelian of prime order and the indicated rank. -/
def isElementaryAbelianOfRank {G : Type*} [Group G]
    (p r : ℕ) (H : Subgroup G) : Prop :=
  Nat.Prime p ∧
    Nat.card H = p ^ r ∧
    (∀ x y : H, x * y = y * x) ∧
    (∀ x : H, x ^ p = 1)

/-- The full preimage of a subgroup under the block action, written in the
ambient permutation group so that it is the stated `rho⁻¹(Q)`. -/
def isFullPreimage {Ω : Type*} {B : Type*}
    (Y : Subgroup (Equiv.Perm Ω))
    (rho : Y →* Equiv.Perm B) (Q : Subgroup (Equiv.Perm B))
    (W : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ w, w ∈ W ↔
    w ∈ Y ∧ ∃ hw : w ∈ Y, rho ⟨w, hw⟩ ∈ Q

/-- A subgroup complement to `D` in `W`. -/
def hasSubgroupComplement {Ω : Type*}
    (D W : Subgroup (Equiv.Perm Ω)) : Prop :=
  D ≤ W ∧
    ∃ C : Subgroup W,
      (∀ c : C, ((c : W) : Equiv.Perm Ω) ∈ D → (c : W) = 1) ∧
      (∀ w : W, ∃ d : D, ∃ c : C,
        (w : Equiv.Perm Ω) = (d : Equiv.Perm Ω) * ((c : W) : Equiv.Perm Ω))

/-- The regular coordinates identify `Q` with the additive vector space and
make its actual action the corresponding translation action. -/
def isRegularQCoordinates {p m : ℕ} {B : Type*}
    (Q : Subgroup (Equiv.Perm B))
    (coord : B ≃ (Fin m → ZMod p))
    (qLabel : Q → (Fin m → ZMod p)) : Prop :=
  Function.Bijective qLabel ∧
    (∀ q r : Q, qLabel (q * r) = qLabel q + qLabel r) ∧
    qLabel 1 = 0 ∧
    (∀ q : Q, ∀ b : B,
      coord ((q : Equiv.Perm B) b) = qLabel q + coord b)

/-- The chosen fibre origins and the resulting `Ω = F_p × E` coordinates. -/
def isFibreCoordinates {p : ℕ} {Ω B E : Type*}
    (z : Equiv.Perm Ω) (origin : B → Ω) (blockOf : Ω → B)
    (coord : B ≃ E) (omegaCoord : Ω ≃ ZMod p × E) : Prop :=
  (∀ B, omegaCoord (origin B) = (0, coord B)) ∧
    (∀ ω, omegaCoord (z ω) =
      ((omegaCoord ω).1 + 1, (omegaCoord ω).2)) ∧
    (∀ ω, coord (blockOf ω) = (omegaCoord ω).2)

/-- The section `M(x,y)` from the graph in the selected fibre coordinates. -/
def graphSection {p : ℕ} {Ω E : Type*}
    (Γ : SimpleGraph Ω) (omegaCoord : Ω ≃ ZMod p × E)
    (x y : E) : Set (ZMod p) :=
  {δ | Γ.Adj (omegaCoord.symm (0, x)) (omegaCoord.symm (δ, y))}

/-- The section obtained by changing the fibre origins by a vertex function. -/
def gaugeSection {E : Type*} [AddCommGroup E]
    (M : E → E → Set (ZMod p)) (b : E → ZMod p)
    (x y : E) : Set (ZMod p) :=
  {δ | ∃ μ, μ ∈ M x y ∧ δ = μ + b x - b y}

/-- The exact translation-invariance condition for a section system. -/
def isTranslationInvariant {E : Type*} [AddGroup E]
    (M : E → E → Set (ZMod p)) : Prop :=
  ∀ x y t, M (x + t) (y + t) = M x y

/-- The exact Cayley-section condition. -/
def isCayleySectionSystem {E : Type*} [AddGroup E]
    (M : E → E → Set (ZMod p)) : Prop :=
  ∀ x y, M x y = M 0 (y - x)

/-- Claim 61384: in a connected semiregular prime layer, the full preimage is
 elementary abelian exactly when the section system is translation-gauge
 equivalent to a Cayley section system. -/
def claim61384 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω] (Γ : SimpleGraph Ω)
    (p m : ℕ) (A D Y W : Subgroup (Equiv.Perm Ω)) (z : Equiv.Perm Ω),
    Nat.Prime p →
    isGraphAutomorphismGroup Γ A →
    z ∈ A →
    D = Subgroup.closure ({z} : Set (Equiv.Perm Ω)) →
    D ≤ A →
    isSemiregular D →
    Nat.card D = p →
    isCentralizer A D Y →
    D ≤ Y →
    W ≤ Y →
    ∀ (rho : Y →* Equiv.Perm (orbitBlocks D)),
      inducesOrbitAction D Y rho →
      (∀ y : Y, y ∈ rho.ker ↔ (y : Equiv.Perm Ω) ∈ D) →
      ∀ (Q : Subgroup (Equiv.Perm (orbitBlocks D))),
        Q ≤ rho.range →
        isRegular Q →
        isElementaryAbelianOfRank p m Q →
        isFullPreimage Y rho Q W →
        D ≤ W →
        ∀ (coord : orbitBlocks D ≃ (Fin m → ZMod p))
          (qLabel : Q → (Fin m → ZMod p)),
          isRegularQCoordinates Q coord qLabel →
          ∀ (origin : orbitBlocks D → Ω) (blockOf : Ω → orbitBlocks D),
            isOrbitMap D blockOf →
            isOriginChoice D origin blockOf →
            ∀ (omegaCoord : Ω ≃ ZMod p × (Fin m → ZMod p)),
              isFibreCoordinates z origin blockOf coord omegaCoord →
              let M := graphSection Γ omegaCoord
              (isElementaryAbelianOfRank p (m + 1) W ↔
                hasSubgroupComplement D W) ∧
              (hasSubgroupComplement D W ↔
                ∃ b : (Fin m → ZMod p) → ZMod p,
                  isTranslationInvariant (gaugeSection M b)) ∧
              ((∃ b : (Fin m → ZMod p) → ZMod p,
                  isTranslationInvariant (gaugeSection M b)) ↔
                ∃ b : (Fin m → ZMod p) → ZMod p,
                  isCayleySectionSystem (gaugeSection M b))

end
end MathlibPlus.Open.Research.CIGainElementaryPreimageGauge
