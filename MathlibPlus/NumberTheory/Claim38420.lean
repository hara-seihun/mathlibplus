import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory.Claim38420

theorem exists_sum_two_squares_neg_one_of_odd_prime
    {p : ℕ} (hp : Nat.Prime p) (_hodd : Odd p) :
    ∃ a b : ZMod p, a ^ 2 + b ^ 2 = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa using (ZMod.sq_add_sq p (-1 : ZMod p))

end MathlibPlus.NumberTheory.Claim38420
