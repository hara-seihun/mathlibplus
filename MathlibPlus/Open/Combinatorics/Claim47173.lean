import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Claim 47173: endpoint insertion is governed exactly by the old positive
partial-sum list. -/
def claim47173 : Prop :=
  ∀ {G : Type*} [AddCommGroup G] (B : List G) (a : G),
    B ≠ [] →
    let P : List G :=
      (List.scanl (fun s x => s + x) 0 B).tail
    let T : G := B.sum
    P.Nodup →
      ((List.scanl (fun s x => s + x) (0 : G) (a :: B)).tail.Nodup ↔
        0 ∉ P) ∧
      ((List.scanl (fun s x => s + x) (0 : G) (B ++ [a])).tail.Nodup ↔
        T + a ∉ P) ∧
      ((List.scanl (fun s x => s + x) (0 : G) (a :: B)).tail =
        a :: P.map (fun q => a + q)) ∧
      ((List.scanl (fun s x => s + x) (0 : G) (B ++ [a])).tail =
        P ++ [T + a]) ∧
      (∀ p q : G, p ∈ P → q ∈ P →
        (a + p) - (a + q) = p - q)

end MathlibPlus.Open.Combinatorics
