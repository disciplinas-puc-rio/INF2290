import KolmogorovBounds.PrimeNumbers.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic

set_option linter.style.header false
set_option linter.style.longLine false

namespace KolmogorovBounds

/-!
# Escopo 1: Lemas Matemáticos (Teoria dos Números e Códigos - Exercícios 9.1 a 9.6)
-/

/--
Exercício 9.3 (Parte 1 - O Algoritmo): Dada uma função `p` que devolve o m-ésimo primo (`p m`),o algoritmo reconstrói `n` multiplicando `f m` pelo quociente `k`.
-/
def reconstructFromPrime (f : ℕ -> ℕ) (m k : ℕ) : ℕ :=
  (f m) * k

/--
Exercício 9.5 (Parte 1 - O Código Iterado):
Em vez de usar `barCode` na etiqueta `bin(|w|)`, aplicamos o próprio `selfTermCode`
na etiqueta `bin(|w|)`.
-/
def iteratedCode (bin : ℕ → Word) (w : Word) : Word :=
  selfTermCode bin (bin w.length) ++ w

end KolmogorovBounds
