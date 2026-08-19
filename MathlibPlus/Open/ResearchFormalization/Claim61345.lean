import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61345

noncomputable section

def exactPrimeOrder61345
    {V : Type*} [AddCommGroup V]
    (q : ℕ) (alpha : V ≃+ V) : Prop :=
  alpha.toEquiv ^ q = Equiv.refl V ∧
    ∀ k : ℕ, 0 < k → k < q →
      alpha.toEquiv ^ k ≠ Equiv.refl V

def fixedPointFree61345
    {V : Type*} [AddCommGroup V] (alpha : V ≃+ V) : Prop :=
  ∀ v : V, alpha v = v → v = 0

def scalarAffineTwist61345
    {V B : Type*} [AddCommGroup V]
    (q : ℕ) (alpha : V ≃+ V)
    (phi : B → ZMod q) (c : B → V) : V × B → V × B :=
  fun p =>
    ((alpha.toEquiv ^ (phi p.2).val) p.1 + c p.2, p.2)

def cayleyDigraphIso61345
    {G : Type*} [AddCommGroup G]
    (f : G → G) (S T : Set G) : Prop :=
  ∀ x y : G, y - x ∈ S ↔ f y - f x ∈ T

def identityFree61345
    {G : Type*} [AddCommGroup G] (S : Set G) : Prop :=
  (0 : G) ∉ S

/-- Claim 61345: arbitrary scalar-exponent and translation tables on a
    fixed-point-free prime-order factor cannot move any simultaneously carried
    identity-free directed Cayley connection set. -/
def scalarAffineTwistCollapse_claim61345 : Prop :=
  ∀ (B V : Type*) [Fintype B] [Fintype V]
    [AddCommGroup B] [AddCommGroup V],
    Nat.Coprime (Fintype.card B) (Fintype.card V) →
      ∀ q : ℕ, Nat.Prime q →
        ∀ alpha : V ≃+ V,
          exactPrimeOrder61345 q alpha →
            fixedPointFree61345 alpha →
              ∀ (phi : B → ZMod q) (c : B → V),
                phi 0 = 0 → c 0 = 0 →
                  ∀ (I : Type*) [Fintype I]
                    (S T : I → Set (V × B)),
                    (∀ i : I,
                      identityFree61345 (S i) ∧
                        identityFree61345 (T i)) →
                      (∀ i : I, ∀ x y : V × B,
                        y - x ∈ S i ↔
                          scalarAffineTwist61345 q alpha phi c y -
                            scalarAffineTwist61345 q alpha phi c x ∈ T i) →
                        ∀ i : I, S i = T i

end

end MathlibPlus.Open.ResearchFormalization.Claim61345
