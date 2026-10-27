import KolmogorovBounds.PrimeNumbers.Basic
import KolmogorovBounds.PrimeNumbers.Lemma
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic

/-!
# Teoremas sobre Números Primos e Complexidade de Kolmogorov
-/
namespace KolmogorovBounds


set_option linter.style.header false
set_option linter.style.longLine false


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
  exact Nat.le_trans h_bound h_step -- aplica a propriedade transitiva da desigualdade (se $A \le B$ e $B \le C$, então $A \le C$). Ele junta o limite inicial h_bound com o nosso novo passo h_step, fechando a prova.

/--
Exercício 9.4 (Parte 1 - Lema Auxiliar):
A codificação `\overline{w}` (`barCode`) dobra exatamente o tamanho de qualquer palavra `w`:
`|\overline{w}| = 2 * |w|`.
-/
theorem barCode_length (w : Word) :
    (barCode w).length = 2 * w.length := by
  match w with
  | [ ] => rfl
  | [a] => rfl
  | a :: b :: as =>
      simp [barCode_length (b :: as), barCode]
      omega

/--
Exercício 9.4 (Parte 2 - Tamanho de `code(w)`):
O comprimento de `code(w) = \overline{bin(|w|)} ++ w` é `2 * |bin(|w|)| + |w|`.
-/
theorem ex_9_4_code_length (bin : ℕ → Word) (w : Word) :
    (selfTermCode bin w).length = 2 * (bin w.length).length + w.length := by
  unfold selfTermCode
  rw [List.length_append]
  rw [barCode_length]

/--
Exercício 9.4 (Parte 3 - O Limite do m-ésimo Primo em forma logarítmica):
Se `log_n ≤ K_n` (incompressível) e `K_n ≤ (2 * log_log_m + log_m) + (log_n - log_pm)`,
então `log_pm ≤ log_m + 2 * log_log_m` (que equivale a `p_m ≤ m * log^2(m)`).
-/
theorem ex_9_4_prime_bound (K_n log_n log_pm log_m log_log_m : ℕ)
    (h_div_le : log_pm ≤ log_n)
    (h_incomp : IsIncompressibleNat K_n log_n)
    (h_code_bound : K_n ≤ (2 * log_log_m + log_m) + (log_n - log_pm)) :
    log_pm ≤ log_m + 2 * log_log_m := by
  unfold IsIncompressibleNat at h_incomp
  omega

/--
Exercício 9.5 (Parte 2 - Tamanho do Código Iterado):
O tamanho do código iterado é `2 * |bin(|bin(|w|)|)| + |bin(|w|)| + |w|`.
-/
theorem ex_9_5_iterated_length (bin : ℕ → Word) (w : Word) :
    (iteratedCode bin w).length =
      2 * (bin (bin w.length).length).length + (bin w.length).length + w.length := by
  unfold iteratedCode
  rw [List.length_append]
  rw [ex_9_4_code_length]

/--
Exercício 9.5 (Parte 3 - O Novo Limite Melhorado dos Primos):
Substituindo o código iterado na desigualdade de Kolmogorov, obtemos:
`log_pm ≤ log_m + log_log_m + 2 * log_log_log_m`
(que corresponde a `p_m ≤ m * log(m) * (log log m)^2`).
-/
theorem ex_9_5_improved_prime_bound
    (K_n log_n log_pm log_m log_log_m log_log_log_m : ℕ)
    (h_div_le : log_pm ≤ log_n)
    (h_incomp : IsIncompressibleNat K_n log_n)
    (h_code_bound : K_n ≤ (2 * log_log_log_m + log_log_m + log_m) + (log_n - log_pm)) :
    log_pm ≤ log_m + log_log_m + 2 * log_log_log_m := by
  unfold IsIncompressibleNat at h_incomp
  omega

/--
Exercício 9.6:
Se `n` é incompressível (`K_n ≥ log_n`), e ser primo permite descrever `n`
apenas pelo seu índice `m = pi(n)` gastando `K_n ≤ log_m` bits,
então para `n` suficientemente grande (onde pelo Teorema dos Números Primos `log_m < log_n`),
`n` NÃO pode ser primo (`¬ Nat.Prime n`).
-/
theorem ex_9_6_incompressible_not_prime (n K_n log_n log_m : ℕ)
    (h_incomp : IsIncompressibleNat K_n log_n)
    (h_prime_encoding : Nat.Prime n → K_n ≤ log_m)
    (h_pnt_large : log_m < log_n) :
    ¬ Nat.Prime n := by
  intro h_is_prime
  unfold IsIncompressibleNat at h_incomp
  have h := h_prime_encoding h_is_prime
  omega

end KolmogorovBounds
