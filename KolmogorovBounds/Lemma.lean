import KolmogorovBounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic

namespace KolmogorovBounds

/-!
# Escopo 1: Lemas Matemáticos (Teoria dos Números e Códigos - Exercícios 9.1 a 9.6)
-/

/--
Exercício 9.3 (Parte 1 - O Algoritmo): Dada uma função `p` que devolve o m-ésimo primo (`p m`),o algoritmo reconstrói `n` multiplicando `f m` pelo quociente `k`.
-/
def reconstructFromPrime (f : ℕ -> ℕ) (m k : ℕ) : ℕ :=
  (f m) * k

end KolmogorovBounds
