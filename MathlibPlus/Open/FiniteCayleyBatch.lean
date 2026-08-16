import Mathlib

namespace MathlibPlus.Open

/-- Claim 60204: the valency-seven CI assertion for the specified semidirect product. -/
def cayley_ci_e_c35_8_valency_seven : Prop :=
  let E := ZMod 35 × ZMod 8
  let one : E := (0, 0)
  let mul : E → E → E := fun x y =>
    (x.1 + (if x.2.val % 2 = 0 then y.1 else -y.1), x.2 + y.2)
  let inv : E → E := fun x =>
    (if x.2.val % 2 = 0 then -x.1 else x.1, -x.2)
  let adj : Set E → E → E → Prop := fun U x y =>
    x ≠ y ∧ ∃ s ∈ U, y = mul x s
  let iso : Set E → Set E → Prop := fun U V =>
    ∃ f : E → E,
      Function.Bijective f ∧
        ∀ x y, adj U x y ↔ adj V (f x) (f y)
  let aut : (E → E) → Prop := fun f =>
    Function.Bijective f ∧
      f one = one ∧
        ∀ x y, f (mul x y) = mul (f x) (f y)
  ∀ S T : Set E,
    S ⊆ ({one} : Set E)ᶜ ∧
      T ⊆ ({one} : Set E)ᶜ ∧
        (∀ s ∈ S, inv s ∈ S) ∧
          (∀ t ∈ T, inv t ∈ T) ∧
            S.ncard = 7 ∧ T.ncard = 7 ∧
              iso S T →
                ∃ f : E → E, aut f ∧ f '' S = T

/-- Claim 60205: the valency-eight CI assertion in the six-dimensional binary cell. -/
def cayley_ci_f2_six_valency_eight : Prop :=
  let V := Fin 6 → ZMod 2
  let adj : Set V → V → V → Prop := fun U x y =>
    x ≠ y ∧ ∃ s ∈ U, y = x + s
  let iso : Set V → Set V → Prop := fun U W =>
    ∃ f : V → V,
      Function.Bijective f ∧
        ∀ x y, adj U x y ↔ adj W (f x) (f y)
  ∀ S T : Set V,
    S ⊆ ({0} : Set V)ᶜ ∧
      T ⊆ ({0} : Set V)ᶜ ∧
        S.ncard = 8 ∧ T.ncard = 8 ∧
          Submodule.span (ZMod 2) S = ⊤ ∧
            Submodule.span (ZMod 2) T = ⊤ ∧
              iso S T →
                ∃ A : V ≃ₗ[ZMod 2] V, A '' S = T

/-- Claim 60206: all elementary-abelian ternary connection sets of size at most eight are CI,
with the stated valency consequence. -/
def cayley_ci_f3_small_valency : Prop :=
  ∀ r : ℕ,
    let V := Fin r → ZMod 3
    let adj : Set V → V → V → Prop := fun U x y =>
      x ≠ y ∧ ∃ s ∈ U, y = x + s
    let iso : Set V → Set V → Prop := fun U W =>
      ∃ f : V → V,
        Function.Bijective f ∧
          ∀ x y, adj U x y ↔ adj W (f x) (f y)
    let connection : Set V → Prop := fun U =>
      U ⊆ ({0} : Set V)ᶜ ∧ ∀ s ∈ U, -s ∈ U
    (∀ S T : Set V,
      connection S ∧ connection T ∧ S.ncard ≤ 8 ∧ iso S T →
        ∃ A : V ≃ₗ[ZMod 3] V, A '' S = T) ∧
      (∀ S T : Set V,
        connection S ∧ connection T ∧ iso S T ∧
              (¬ ∃ A : V ≃ₗ[ZMod 3] V, A '' S = T) →
          10 ≤ S.ncard)

/-- Claim 60207: the exact minimum valency seven and the displayed witness in the order-50
semidirect product. -/
def cayley_nonci_f5_two_by_c2_minimum_seven : Prop :=
  let H := (ZMod 3)ˣ × (Fin 2 → ZMod 5)
  let one : H := (1, 0)
  let mul : H → H → H := fun x y =>
    (x.1 * y.1, x.2 + (if x.1 = 1 then y.2 else -y.2))
  let inv : H → H := fun x =>
    (x.1⁻¹, if x.1 = 1 then -x.2 else x.2)
  let adj : Set H → H → H → Prop := fun U x y =>
    x ≠ y ∧ ∃ s ∈ U, y = mul x s
  let iso : Set H → Set H → Prop := fun U V =>
    ∃ f : H → H,
      Function.Bijective f ∧
        ∀ x y, adj U x y ↔ adj V (f x) (f y)
  let aut : (H → H) → Prop := fun f =>
    Function.Bijective f ∧
      f one = one ∧
        ∀ x y, f (mul x y) = mul (f x) (f y)
  let connection : Set H → Prop := fun U =>
    U ⊆ ({one} : Set H)ᶜ ∧ ∀ s ∈ U, inv s ∈ U
  let nonCI : Set H → Set H → Prop := fun U V =>
    iso U V ∧ ¬ ∃ f : H → H, aut f ∧ f '' U = V
  let vector : ZMod 5 → ZMod 5 → (Fin 2 → ZMod 5) := fun x y i =>
    if i = (0 : Fin 2) then x else y
  let f : ZMod 5 → ZMod 5 := fun x => 3 * x ^ 2 + 2 * x
  let g : ZMod 5 → ZMod 5 := fun x => x ^ 2 + 4 * x
  let R : Set H :=
    {(1, vector 0 1), (1, vector 0 (-1))}
  let S : Set H :=
    R ∪ {p : H | ∃ x : ZMod 5, p = (-1, vector x (f x))}
  let T : Set H :=
    R ∪ {p : H | ∃ x : ZMod 5, p = (-1, vector x (g x))}
  (∀ U V : Set H,
      connection U ∧ connection V ∧
          U.ncard = V.ncard ∧ U.ncard ≤ 6 →
        ¬ nonCI U V) ∧
    connection S ∧ connection T ∧
      S.ncard = 7 ∧ T.ncard = 7 ∧ nonCI S T

end MathlibPlus.Open
