import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- The prefix-sum notion of a strong ordering from claim R-3412.1. -/
def strongOrdering {G : Type*} [AddCommGroup G] (B : List G) : Prop :=
  (List.scanl (fun s a => s + a) 0 B).Nodup

/-- The prefix-sum notion of a valid ordering from claim R-3412.1. -/
def validOrdering {G : Type*} [AddCommGroup G] (B : List G) : Prop :=
  (List.scanl (fun s a => s + a) 0 B).tail.Nodup

end MathlibPlus.Combinatorics
