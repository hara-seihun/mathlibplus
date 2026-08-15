import Mathlib

namespace MathlibPlus.Open.Combinatorics.D0074

def claim4997 : Prop :=
  let isoRel : ∀ n : ℕ, SimpleGraph (Fin n) → SimpleGraph (Fin n) → Prop :=
    fun n G H => ∃ e : Fin n ≃ Fin n, ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)
  let graphClass : ℕ → Type := fun n => Quot (isoRel n)
  let V : ℕ → Type := fun n => Finsupp (graphClass n) ℚ
  let autWeight : ∀ n : ℕ, graphClass n → ℚ :=
    fun n G => Nat.card {e : Fin n ≃ Fin n // ∀ v w, (Quot.out G).Adj v w ↔ (Quot.out G).Adj (e v) (e w)}
  let deleteGraph : ∀ {n : ℕ}, SimpleGraph (Fin (n + 1)) → Fin (n + 1) → SimpleGraph (Fin n) :=
    fun {n} G v => G.comap (Fin.succAboveEmb v)
  let insertGraph : ∀ {n : ℕ}, SimpleGraph (Fin n) → Finset (Fin n) → SimpleGraph (Fin (n + 1)) :=
    fun {n} H S => SimpleGraph.fromRel (fun a b =>
      if ha : a = 0 then
        if hb : b = 0 then False else Fin.pred b hb ∈ S
      else if hb : b = 0 then
        Fin.pred a ha ∈ S
      else H.Adj (Fin.pred a ha) (Fin.pred b hb))
  let deck : ∀ n : ℕ, V (n + 1) → V n :=
    fun n x => x.sum (fun G c =>
      ∑ v : Fin (n + 1),
        Finsupp.single (Quot.mk (isoRel n) (deleteGraph (Quot.out G) v)) c)
  let insert : ∀ n : ℕ, V n → V (n + 1) :=
    fun n x => x.sum (fun H c =>
      ∑ S : Finset (Fin n),
        Finsupp.single (Quot.mk (isoRel (n + 1)) (insertGraph (Quot.out H) S)) c)
  let pairing : ∀ n : ℕ, V n → V n → ℚ :=
    fun n x y => x.sum (fun G c => c * y G * autWeight n G)
  ∀ n : ℕ, ∀ x : V n, ∀ y : V (n + 1),
    pairing (n + 1) (insert n x) y = pairing n x (deck n y)

def claim4998 : Prop :=
  let isoRel : ∀ n : ℕ, SimpleGraph (Fin n) → SimpleGraph (Fin n) → Prop :=
    fun n G H => ∃ e : Fin n ≃ Fin n, ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)
  let graphClass : ℕ → Type := fun n => Quot (isoRel n)
  let autWeight : ∀ n : ℕ, graphClass n → ℚ :=
    fun n G => Nat.card {e : Fin n ≃ Fin n // ∀ v w, (Quot.out G).Adj v w ↔ (Quot.out G).Adj (e v) (e w)}
  let deleteGraph : ∀ {n : ℕ}, SimpleGraph (Fin (n + 1)) → Fin (n + 1) → SimpleGraph (Fin n) :=
    fun {n} G v => G.comap (Fin.succAboveEmb v)
  let insertGraph : ∀ {n : ℕ}, SimpleGraph (Fin n) → Finset (Fin n) → SimpleGraph (Fin (n + 1)) :=
    fun {n} H S => SimpleGraph.fromRel (fun a b =>
      if ha : a = 0 then
        if hb : b = 0 then False else Fin.pred b hb ∈ S
      else if hb : b = 0 then
        Fin.pred a ha ∈ S
      else H.Adj (Fin.pred a ha) (Fin.pred b hb))
  ∀ n : ℕ,
    letI : Fintype (graphClass n) := Fintype.ofFinite (graphClass n)
    letI : Fintype (graphClass (n + 1)) := Fintype.ofFinite (graphClass (n + 1))
    letI : DecidableEq (graphClass n) := Classical.decEq (graphClass n)
    letI : DecidableEq (graphClass (n + 1)) := Classical.decEq (graphClass (n + 1))
    let d : graphClass (n + 1) → graphClass n → ℚ := fun G H =>
      ∑ v : Fin (n + 1),
        if Quot.mk (isoRel n) (deleteGraph (Quot.out G) v) = H then 1 else 0
    let u : graphClass n → graphClass (n + 1) → ℚ := fun H G =>
      ∑ S : Finset (Fin n),
        if Quot.mk (isoRel (n + 1)) (insertGraph (Quot.out H) S) = G then 1 else 0
    let D : Matrix (graphClass n) (graphClass (n + 1)) ℚ := fun H G => d G H
    let U : Matrix (graphClass (n + 1)) (graphClass n) ℚ := fun G H => u H G
    let A_n : Matrix (graphClass n) (graphClass n) ℚ := fun G H =>
      if G = H then autWeight n G else 0
    let A_n1 : Matrix (graphClass (n + 1)) (graphClass (n + 1)) ℚ := fun G H =>
      if G = H then autWeight (n + 1) G else 0
    D = A_n⁻¹ * Matrix.transpose U * A_n1

end MathlibPlus.Open.Combinatorics.D0074
