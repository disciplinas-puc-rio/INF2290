import Mathlib.Data.Nat.Basic
import KolmogorovBounds.Basic
import KolmogorovBounds.Lemma
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic

set_option linter.style.longLine false

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

/--
Exercício 9.2:
Se o m-ésimo primo `p_m` satisfaz `p_m ≤ m * log_m^2`, então escolhendo `n = p_m`
(onde `pi_n = m` e `log_m ≤ log_n`), obtemos `n ≤ pi_n * log_n^2`
(que é a forma sem frações de `pi(n) ≥ n / log^2(n)`).
-/
theorem ex_9_2_sufficiency (n p_m m pi_n log_m log_n : ℕ)
    (h_n : n = p_m)
    (h_pi : pi_n = m)
    (h_bound : p_m ≤ m * log_m ^ 2)
    (h_log_mono : log_m ^ 2 ≤ log_n ^ 2) :
    n ≤ pi_n * log_n ^ 2 := by
  rw [h_n, h_pi] -- reescreve o objetivo final, substituindo as variáveis genéricas n e pi_n pelos seus correspondentes na hipótese (p_m e m). O objetivo passa a ser exatamente p_m ≤ m * log_n ^ 2.
  have h_step : m * log_m ^ 2 ≤ m * log_n ^ 2 := Nat.mul_le_mul_left m h_log_mono -- cria-se um passo intermédio. Como já sabemos que log_m ^ 2 ≤ log_n ^ 2 (através do h_log_mono), utilizamos o lema Nat.mul_le_mul_left m para multiplicar o termo m em ambos os lados da inequação, provando que m * log_m ^ 2 ≤ m * log_n ^ 2.
  exact Nat.le_trans h_bound h_step -- aplica a propriedade transitiva da desigualdade (se $A \le B$ e $B \le C$, então $A \le C$). Ele junta o limite inicial h_bound com o nosso novo passo h_step, fechando a prova com sucesso.


end KolmogorovBounds.Theorem
