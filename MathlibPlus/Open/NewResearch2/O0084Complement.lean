import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.NewResearch2.O0084Complement

private def primePrefix (y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter Nat.Prime

private def primorial (y : ℕ) : ℕ :=
  (primePrefix y).prod (fun p => p)

private def primeCount (y : ℕ) : ℕ :=
  (primePrefix y).card

private def finiteMobiusPort (y : ℕ) (t : ℂ) : ℂ :=
  ((primorial y).divisors).sum (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℂ) * Complex.exp (- (d : ℂ) * t))

private def h (x : ℂ) : ℂ :=
  Complex.exp (-x) - 1 + x

private def eulerPrefix (y k : ℕ) : ℂ :=
  (primePrefix y).prod (fun p => (1 : ℂ) - (p : ℂ)⁻¹ ^ k)

private def reciprocalEulerPrefix (y : ℕ) : ℂ :=
  (primePrefix y).prod (fun p => (1 : ℂ) - (p : ℂ)⁻¹)

private def remainder (y : ℕ) (x : ℂ) : ℂ :=
  ((-1 : ℂ) ^ primeCount y) * finiteMobiusPort y (x / (primorial y : ℂ)) +
    x * reciprocalEulerPrefix y

private def finiteTaylorSeries (y : ℕ) (x : ℂ) : ℂ :=
  ∑' k : ℕ, if 2 ≤ k then
    (-x) ^ k * eulerPrefix y k / (k.factorial : ℂ)
  else 0

private def positiveMobiusKernel (x : ℂ) : ℂ :=
  ∑' n : ℕ, if 1 ≤ n then
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) * h (x / (n : ℂ))
  else 0

private def reciprocalZetaTaylorSeries (x : ℂ) : ℂ :=
  ∑' k : ℕ, if 2 ≤ k then
    (-x) ^ k / ((k.factorial : ℂ) * riemannZeta (k : ℂ))
  else 0

 def claim13386 : Prop :=
  ∀ (y : ℕ) (x : ℂ),
    ((-1 : ℂ) ^ primeCount y) * finiteMobiusPort y (x / (primorial y : ℂ)) =
      ((primorial y).divisors).sum (fun e =>
        ((ArithmeticFunction.moebius e : ℤ) : ℂ) * Complex.exp (-x / (e : ℂ)))

 def claim13388 : Prop :=
  ∀ (y : ℕ) (x : ℂ),
    remainder y x =
      ((primorial y).divisors).sum (fun e =>
        ((ArithmeticFunction.moebius e : ℤ) : ℂ) * h (x / (e : ℂ)))

 def claim13389 : Prop :=
  ∀ (y : ℕ) (x : ℂ),
    remainder y x = finiteTaylorSeries y x

 def claim13392 : Prop :=
  ∀ (x : ℂ),
    positiveMobiusKernel x = reciprocalZetaTaylorSeries x

end MathlibPlus.Open.NewResearch2.O0084Complement

end
