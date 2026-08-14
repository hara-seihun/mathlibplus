import Mathlib

noncomputable section

namespace MathlibPlus.Open.NewResearch2.GDP

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The exact m-state forest polynomial, with A0 the complement and one shared cut variable. -/
def claim_16309 : Prop :=
  ∀ (n : ℕ) (F : SimpleGraph (Fin n)) (m : ℕ),
    F.IsAcyclic → 0 < m →
      let Var := Sum Unit (Fin m × Bool)
      let pairs := Finset.univ.filter (fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ F.Adj p.1 p.2)
      let internal := fun A : Finset (Fin n) =>
        (pairs.filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card
      let boundary := fun A : Fin m → Finset (Fin n) =>
        (pairs.filter (fun p => ¬ ∀ i : Fin m,
          (p.1 ∈ A i ↔ p.2 ∈ A i))).card
      ∃! P : MvPolynomial Var ℕ,
        P = ∑ A : Fin m → Finset (Fin n),
          if (∀ i j : Fin m, i ≠ j → Disjoint (A i) (A j)) then
            (∏ i : Fin m, MvPolynomial.X (Sum.inr (i, false)) ^ (A i).card) *
              (∏ i : Fin m, MvPolynomial.X (Sum.inr (i, true)) ^ internal (A i)) *
              MvPolynomial.X (Sum.inl ()) ^ boundary A
          else 0

/-- A concrete ordinary-GDP collision between nonisomorphic finite trees. -/
def claim_16312 : Prop :=
  ∃ (n : ℕ) (F H : SimpleGraph (Fin n)),
    F.IsTree ∧ H.IsTree ∧
    (¬ ∃ e : Fin n ≃ Fin n, ∀ x y : Fin n,
      F.Adj x y ↔ H.Adj (e x) (e y)) ∧
    (let gdp : SimpleGraph (Fin n) → MvPolynomial (Fin 3) ℕ := (fun (G : SimpleGraph (Fin n)) =>
      let pairs := Finset.univ.filter (fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ G.Adj p.1 p.2)
      ∑ A : Finset (Fin n),
        MvPolynomial.X (0 : Fin 3) ^ A.card *
          MvPolynomial.X (1 : Fin 3) ^
            (pairs.filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card *
          MvPolynomial.X (2 : Fin 3) ^
            (pairs.filter (fun p => ¬ (p.1 ∈ A ↔ p.2 ∈ A))).card)
      ; gdp F = gdp H)

/-- The ordinary collision persists after attaching the same rooted leaf family. -/
def claim_16313 : Prop :=
  ∃ (n : ℕ) (F H : SimpleGraph (Fin n)) (r s : Fin n),
    F.IsTree ∧ H.IsTree ∧
    (¬ ∃ e : Fin n ≃ Fin n, ∀ x y : Fin n,
      F.Adj x y ↔ H.Adj (e x) (e y)) ∧
    (let gdp : SimpleGraph (Fin n) → MvPolynomial (Fin 3) ℕ := (fun (G : SimpleGraph (Fin n)) =>
      let pairs := Finset.univ.filter (fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ G.Adj p.1 p.2)
      ∑ A : Finset (Fin n),
        MvPolynomial.X (0 : Fin 3) ^ A.card *
          MvPolynomial.X (1 : Fin 3) ^
            (pairs.filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card *
          MvPolynomial.X (2 : Fin 3) ^
            (pairs.filter (fun p => ¬ (p.1 ∈ A ↔ p.2 ∈ A))).card)
      ; gdp F = gdp H) ∧
    ∀ k : ℕ, ∃ Fk Hk : SimpleGraph (Fin n ⊕ Fin k),
      Fk.IsTree ∧ Hk.IsTree ∧
      (∀ u v : Fin n ⊕ Fin k,
        Fk.Adj u v ↔
          match u, v with
          | Sum.inl a, Sum.inl b => F.Adj a b
          | Sum.inl a, Sum.inr _ => a = r
          | Sum.inr _, Sum.inl b => b = r
          | Sum.inr _, Sum.inr _ => False) ∧
      (∀ u v : Fin n ⊕ Fin k,
        Hk.Adj u v ↔
          match u, v with
          | Sum.inl a, Sum.inl b => H.Adj a b
          | Sum.inl a, Sum.inr _ => a = s
          | Sum.inr _, Sum.inl b => b = s
          | Sum.inr _, Sum.inr _ => False) ∧
      (¬ ∃ e : (Fin n ⊕ Fin k) ≃ (Fin n ⊕ Fin k), ∀ x y,
        Fk.Adj x y ↔ Hk.Adj (e x) (e y)) ∧
      (let gdp : SimpleGraph (Fin n ⊕ Fin k) → MvPolynomial (Fin 3) ℕ :=
        (fun (G : SimpleGraph (Fin n ⊕ Fin k)) =>
        let pairs := Finset.univ.filter (fun p : (Fin n ⊕ Fin k) × (Fin n ⊕ Fin k) =>
          p.1 < p.2 ∧ G.Adj p.1 p.2)
        ∑ A : Finset (Fin n ⊕ Fin k),
          MvPolynomial.X (0 : Fin 3) ^ A.card *
            MvPolynomial.X (1 : Fin 3) ^
              (pairs.filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card *
            MvPolynomial.X (2 : Fin 3) ^
              (pairs.filter (fun p => ¬ (p.1 ∈ A ↔ p.2 ∈ A))).card)
        ; gdp Fk = gdp Hk)

/-- The chromatic symmetric function determines every fixed-level GDP through an
    explicit additive convolution/specialization map. -/
def claim_16315 : Prop :=
  ∀ (n m : ℕ), 0 < m →
    let Var := Sum Unit (Fin m × Bool)
    let csf : SimpleGraph (Fin n) → MvPolynomial (Fin n) ℕ := fun G =>
      ∑ c : Fin n → Fin n,
        if (∀ u v : Fin n, G.Adj u v → c u ≠ c v) then
          ∏ v : Fin n, (MvPolynomial.X (c v) : MvPolynomial (Fin n) ℕ)
        else 0
    let gdp : SimpleGraph (Fin n) → MvPolynomial Var ℕ := fun G =>
      let pairs := Finset.univ.filter (fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ G.Adj p.1 p.2)
      let internal := fun A : Finset (Fin n) =>
        (pairs.filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card
      let boundary := fun A : Fin m → Finset (Fin n) =>
        (pairs.filter (fun p => ¬ ∀ i : Fin m,
          p.1 ∈ A i ↔ p.2 ∈ A i)).card
      ∑ A : Fin m → Finset (Fin n),
        if (∀ i j : Fin m, i ≠ j → Disjoint (A i) (A j)) then
          (∏ i : Fin m, MvPolynomial.X (Sum.inr (i, false)) ^ (A i).card) *
            (∏ i : Fin m, MvPolynomial.X (Sum.inr (i, true)) ^ internal (A i)) *
            MvPolynomial.X (Sum.inl ()) ^ boundary A
        else 0
    ∃ γ : MvPolynomial (Fin n) ℕ →ₗ[ℕ] MvPolynomial Var ℕ,
      ∀ F : SimpleGraph (Fin n), F.IsAcyclic → γ (csf F) = gdp F

/-- The ordinary GDP is obtained by a linear specialization of the tree CSF. -/
def claim_16316 : Prop :=
  ∀ n : ℕ, ∃ γ : MvPolynomial (Fin n) ℕ →ₗ[ℕ] MvPolynomial (Fin 3) ℕ,
    ∀ F : SimpleGraph (Fin n), F.IsAcyclic →
      γ (∑ c : Fin n → Fin n,
        if (∀ u v : Fin n, F.Adj u v → c u ≠ c v) then
          ∏ v : Fin n, (MvPolynomial.X (c v) : MvPolynomial (Fin n) ℕ)
        else 0) =
      (let pairs := Finset.univ.filter (fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ F.Adj p.1 p.2)
       ∑ A : Finset (Fin n),
         MvPolynomial.X (0 : Fin 3) ^ A.card *
           MvPolynomial.X (1 : Fin 3) ^
             (pairs.filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card *
           MvPolynomial.X (2 : Fin 3) ^
             (pairs.filter (fun p => ¬ (p.1 ∈ A ↔ p.2 ∈ A))).card)

/-- A weighted vertex-deleted deck layer can collide on nonisomorphic trees. -/
def claim_16317 : Prop :=
  ∃ (n : ℕ) (F H : SimpleGraph (Fin n)),
    F.IsTree ∧ H.IsTree ∧
    (¬ ∃ e : Fin n ≃ Fin n, ∀ x y : Fin n,
      F.Adj x y ↔ H.Adj (e x) (e y)) ∧
    (let deck : SimpleGraph (Fin n) → Multiset (MvPolynomial (Fin 3) ℕ) := fun (G : SimpleGraph (Fin n)) =>
      let pairs := Finset.univ.filter (fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ G.Adj p.1 p.2)
      let card := fun (v : Fin n) =>
        let kept := pairs.filter (fun p => p.1 ≠ v ∧ p.2 ≠ v)
        ∑ A : Finset (Fin n),
          if v ∉ A then
            MvPolynomial.X (0 : Fin 3) ^ A.card *
              MvPolynomial.X (1 : Fin 3) ^
                (kept.filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card *
              MvPolynomial.X (2 : Fin 3) ^
                (kept.filter (fun p => ¬ (p.1 ∈ A ↔ p.2 ∈ A))).card
          else 0
      Multiset.map card (Finset.univ : Finset (Fin n)).1
     deck F = deck H)

/-- For m=2 the three root-conditioned messages sum to, but refine, the unrooted GDP. -/
def claim_16320 : Prop :=
  ∀ (n : ℕ) (F : SimpleGraph (Fin n)), F.IsAcyclic →
    ∀ root : Fin n,
    (let Var := Sum Unit (Fin 2 × Bool)
     let pairs := Finset.univ.filter (fun p : Fin n × Fin n =>
       p.1 < p.2 ∧ F.Adj p.1 p.2)
     let internal := fun A : Finset (Fin n) =>
       (pairs.filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card
     let boundary := fun A : Fin 2 → Finset (Fin n) =>
       (pairs.filter (fun p => ¬ ∀ i : Fin 2,
         p.1 ∈ A i ↔ p.2 ∈ A i)).card
     let monomial : (Fin 2 → Finset (Fin n)) → MvPolynomial Var ℕ :=
       fun A : Fin 2 → Finset (Fin n) =>
       (∏ i : Fin 2, MvPolynomial.X (Sum.inr (i, false)) ^ (A i).card) *
         (∏ i : Fin 2, MvPolynomial.X (Sum.inr (i, true)) ^ internal (A i)) *
         MvPolynomial.X (Sum.inl ()) ^ boundary A
     let good := fun A : Fin 2 → Finset (Fin n) =>
       ∀ i j : Fin 2, i ≠ j → Disjoint (A i) (A j)
     let rootState := fun (r : Option (Fin 2)) (A : Fin 2 → Finset (Fin n)) =>
       match r with
       | none => ∀ i : Fin 2, root ∉ A i
       | some i => root ∈ A i
     let message : Option (Fin 2) → MvPolynomial Var ℕ := fun r : Option (Fin 2) =>
       ∑ A : Fin 2 → Finset (Fin n),
         @ite _ (good A ∧ rootState r A) (Classical.propDecidable _) (monomial A) 0
     (∑ A : Fin 2 → Finset (Fin n),
         @ite _ (good A) (Classical.propDecidable _) (monomial A) 0) =
       message none + message (some 0) + message (some 1))

/-- On diameter less than six, CSF reconstruction implies the fixed GDP consequences. -/
def claim_16321 : Prop :=
  ∀ (n : ℕ) (F H : SimpleGraph (Fin n)),
    F.IsTree → H.IsTree → F.diam < 6 → H.diam < 6 →
    ((∑ c : Fin n → Fin n,
        if (∀ u v : Fin n, F.Adj u v → c u ≠ c v) then
          ∏ v : Fin n, (MvPolynomial.X (c v) : MvPolynomial (Fin n) ℕ)
        else 0) =
      ∑ c : Fin n → Fin n,
        if (∀ u v : Fin n, H.Adj u v → c u ≠ c v) then
          ∏ v : Fin n, (MvPolynomial.X (c v) : MvPolynomial (Fin n) ℕ)
        else 0) →
    ∃ e : Fin n ≃ Fin n, ∀ x y : Fin n,
      F.Adj x y ↔ H.Adj (e x) (e y)

end MathlibPlus.Open.NewResearch2.GDP
