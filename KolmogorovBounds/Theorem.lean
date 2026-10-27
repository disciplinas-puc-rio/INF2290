import Mathlib.Data.Nat.Basic
import KolmogorovBounds.Basic
import KolmogorovBounds.Lemma
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic

namespace KolmogorovBounds.Theorem

/--
Exercício 9.3:
Se `f m` divide `n` (isto é, `f m ∣ n`), então aplicar o algoritmo de reconstrução
usando `m` e `k = n / f m` devolve exatamente o número original `n`.
-/
theorem ex_9_3_reconstruct_from_prime_correctness (f : ℕ → ℕ) (n m : ℕ) (h_dvd : f m ∣ n) :
  reconstructFromPrime f m (n / f m) = n := by
    unfold reconstructFromPrime
    exact Nat.mul_div_cancel' h_dvd

/--
Exercício 9.1:
Se `n` é incompressível (`K_n ≥ log_n`), mas a existência de apenas `k` primos
permite codificar `n` pelos seus `k` expoentes gastando `K_n ≤ k * code_exp` bits,
então para um `n` suficientemente grande (onde `k * code_exp < log_n`),
temos uma contradição (`False`).
-/
theorem ex_9_1_prime_contradiction (K_n log_n k code_exp : ℕ)
    (h_incomp : IsIncompressibleNat K_n log_n)
    (h_upper_bound : K_n ≤ k * code_exp)
    (h_large_n : k * code_exp < log_n) :
    False := by
  unfold IsIncompressibleNat at h_incomp
  omega

end KolmogorovBounds.Theorem
