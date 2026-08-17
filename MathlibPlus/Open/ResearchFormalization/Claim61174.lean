import Mathlib
import MathlibPlus.Open.Research.H1Shell

namespace MathlibPlus.Open.ResearchFormalization.Claim61174

abbrev EComplement (n : ℕ) := Multiplicative (ZMod n)

abbrev EGroup (K : Type*) [Group K] (n : ℕ)
    (rho : EComplement n →* MulAut K) :=
  SemidirectProduct K (EComplement n) rho

def InversionAction {K : Type*} [Group K] (n : ℕ)
    (rho : EComplement n →* MulAut K) : Prop :=
  ∀ x : K,
    rho (Multiplicative.ofAdd (1 : ZMod n)) x = x⁻¹

def AuxiliaryK (K : Type*) [CommGroup K] [Fintype K] : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ Fintype.card K →
    ∀ P : Sylow p K,
      (IsCyclic P ∧ Nat.card P = p) ∨
        (MathlibPlus.Open.Research.elementaryAbelianSylow p P ∧
          Nat.card P = 9)

abbrev C3Square := Multiplicative (ZMod 3 × ZMod 3)

def IdentityFree (G : Type*) [One G] (S : Set G) : Prop :=
  (1 : G) ∉ S

def InverseClosed (G : Type*) [Inv G] (S : Set G) : Prop :=
  ∀ x, x ∈ S → x⁻¹ ∈ S

def CayleyGraphIsomorphic (G : Type*) [Group G]
    (S T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y,
    (x ≠ y ∧ x⁻¹ * y ∈ S) ↔
      (e x ≠ e y ∧ (e x)⁻¹ * e y ∈ T)

def OrdinaryUndirectedCI (G : Type*) [Group G] : Prop :=
  ∀ S T : Set G,
    IdentityFree G S → IdentityFree G T →
    InverseClosed G S → InverseClosed G T →
    CayleyGraphIsomorphic G S T →
    ∃ α : G ≃* G, α '' S = T

def OrdinaryCIDefectAtValency
    (G : Type*) [Group G] (k : ℕ) : Prop :=
  ∃ (S T : Set G),
    IdentityFree G S ∧ IdentityFree G T ∧
      InverseClosed G S ∧ InverseClosed G T ∧
        Set.ncard S = k ∧ Set.ncard T = k ∧
          CayleyGraphIsomorphic G S T ∧
            ∀ α : G ≃* G, α '' S ≠ T

def LabelledSymmetricBinaryCayleyDefect
    (G : Type*) [Group G] : Prop :=
  ∃ (S T : Fin 2 → Set G) (e : G ≃ G),
    (∀ i, IdentityFree G (S i) ∧ IdentityFree G (T i)) ∧
      (∀ i, InverseClosed G (S i) ∧ InverseClosed G (T i)) ∧
        (∀ i x y,
          (x ≠ y ∧ x⁻¹ * y ∈ S i) ↔
            (e x ≠ e y ∧ (e x)⁻¹ * e y ∈ T i)) ∧
          ¬ ∃ α : G ≃* G, ∀ i, α '' S i = T i

def claim61174 : Prop :=
  (∀ (K : Type*) [CommGroup K] [Fintype K],
      AuxiliaryK K → ¬ IsCyclic K →
        (∃ rho₂ : EComplement 2 →* MulAut K, InversionAction 2 rho₂) ∧
          (∃ rho₄ : EComplement 4 →* MulAut K, InversionAction 4 rho₄) ∧
            ∀ (A : Type*) [Group A] [Fintype A],
              1 < Fintype.card A →
              Nat.Coprime (Fintype.card A) (4 * Fintype.card K) →
              (∀ rho₂ : EComplement 2 →* MulAut K,
                InversionAction 2 rho₂ →
                  Finite (A × EGroup K 2 rho₂) ∧
                    ¬ OrdinaryUndirectedCI
                      (A × EGroup K 2 rho₂)) ∧
              (∀ rho₄ : EComplement 4 →* MulAut K,
                InversionAction 4 rho₄ →
                  Finite (A × EGroup K 4 rho₄) ∧
                    ¬ OrdinaryUndirectedCI
                      (A × EGroup K 4 rho₄))) ∧
  ((∃ rho₂ : EComplement 2 →* MulAut C3Square,
      InversionAction 2 rho₂) ∧
    ∀ rho₂ : EComplement 2 →* MulAut C3Square,
      InversionAction 2 rho₂ →
        Finite (EGroup C3Square 2 rho₂) ∧
          OrdinaryUndirectedCI (EGroup C3Square 2 rho₂)) ∧
  ((∃ rho₄ : EComplement 4 →* MulAut C3Square,
      InversionAction 4 rho₄) ∧
    ∀ rho₄ : EComplement 4 →* MulAut C3Square,
      InversionAction 4 rho₄ →
        Finite (EGroup C3Square 4 rho₄) ∧
          OrdinaryUndirectedCI (EGroup C3Square 4 rho₄)) ∧
  (∃ rho₄ : EComplement 4 →* MulAut C3Square,
      InversionAction 4 rho₄ ∧
        Finite (EGroup C3Square 4 rho₄) ∧
          LabelledSymmetricBinaryCayleyDefect
            (EGroup C3Square 4 rho₄)) ∧
  (∀ rho₄ : EComplement 4 →* MulAut C3Square,
      InversionAction 4 rho₄ →
        LabelledSymmetricBinaryCayleyDefect (EGroup C3Square 4 rho₄)) ∧
  (∀ (A : Type*) [Group A] [Fintype A],
      1 < Fintype.card A →
      Nat.Coprime (Fintype.card A) 36 →
        (∀ rho₂ : EComplement 2 →* MulAut C3Square,
          InversionAction 2 rho₂ →
            Finite (A × EGroup C3Square 2 rho₂) ∧
              ¬ OrdinaryUndirectedCI
                (A × EGroup C3Square 2 rho₂)) ∧
        (∀ rho₄ : EComplement 4 →* MulAut C3Square,
          InversionAction 4 rho₄ →
            Finite (A × EGroup C3Square 4 rho₄) ∧
              ¬ OrdinaryUndirectedCI
                (A × EGroup C3Square 4 rho₄))) ∧
  (∀ (A : Type*) [Group A] [Fintype A],
      1 < Fintype.card A →
      Nat.Coprime (Fintype.card A) 36 →
        ∀ rho₄ : EComplement 4 →* MulAut C3Square,
          InversionAction 4 rho₄ →
            Finite (A × EGroup C3Square 4 rho₄) ∧
              OrdinaryCIDefectAtValency
                (A × EGroup C3Square 4 rho₄) 18)

end MathlibPlus.Open.ResearchFormalization.Claim61174
