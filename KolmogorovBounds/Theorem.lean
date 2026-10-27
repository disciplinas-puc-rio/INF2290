import Mathlib.Data.Nat.Basic
import KolmogorovBounds.Basic
import KolmogorovBounds.Lemma
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic

namespace KolmogorovBounds.Theorem

/--
Exercício 9.3 (Parte 2 - A Prova de Corretude):
Se `f m` divide `n` (isto é, `f m ∣ n`), então aplicar o algoritmo de reconstrução
usando `m` e `k = n / f m` devolve exatamente o número original `n`.
-/
theorem reconstruct_from_prime_correctness (f : ℕ → ℕ) (n m : ℕ) (h_dvd : f m ∣ n) :
  reconstructFromPrime f m (n / f m) = n := by
    unfold reconstructFromPrime
    exact Nat.mul_div_cancel' h_dvd

end KolmogorovBounds.Theorem
