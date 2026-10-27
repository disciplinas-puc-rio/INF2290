import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log

set_option linter.style.header false
set_option linter.style.longLine false

namespace KolmogorovBounds

/-!
# Bloco 1: Strings Binárias e Complexidade de Kolmogorov (A Base Comum)
No texto, tudo é transformado em strings de 0s e 1s (`Word`).
No Lean, representamos uma string binária simplesmente como uma lista de booleanos (`List Bool`).
-/

/-- Uma palavra binária (sequência de 0s e 1s) é uma lista de booleanos. -/
abbrev Word := List Bool

/-- O tamanho `|w|` de uma palavra é o comprimento da lista. -/
def wordLength (w : Word) : ℕ := w.length

/--
Em vez de construir um compilador inteiro dentro do Lean para definir `K(w)`,
modelamos um "Sistema de Complexidade de Kolmogorov" por duas únicas propriedades:

1. Toda palavra tem um custo mínimo de descrição `K(w)`.
2. Uma palavra `w` é "incompressível" (Kolmogorov-aleatória) se `K(w) ≥ |w|`.
-/
structure KolmogorovSystem where
  /-- Função que dá o tamanho da menor receita que gera a palavra `w` -/
  K : Word → ℕ

/-- Uma palavra `x` é Kolmogorov-aleatória (incompressível) se `K(x) ≥ |x|`. -/
def IsIncompressible (sys : KolmogorovSystem) (x : Word) : Prop :=
  sys.K x ≥ x.length

/-- O texto simplifica `|bin(n)| = log n`. Aqui dizemos que um número `n` (com tamanho `log_n`) é incompressível se sua complexidade `K_n` satisfaz `K_n ≥ log_n`.
-/
def IsIncompressibleNat (K_n log_n : ℕ) : Prop :=
  K_n ≥ log_n


/-!
# Bloco 2: Ferramentas do Escopo 1 (Matemático / Códigos Auto-delimitados)

1. O código de barra `\overline{w}`: insere `0` (`false`) após cada bit, exceto o último que leva `1` (`true`).
   (Obs: `\overline{w}` sempre dobra o tamanho: `|\overline{w}| = 2 * |w|`).

2. O código com etiqueta: `code(w) = \overline{bin(|w|)} ++ w`.
-/

/--
Codificação `\overline{w}`:
Para cada bit da palavra, dobramos o tamanho colocando um marcador logo depois.
- Na última letra `[a]`, colocamos `[a, true]` (representando `a1`).
- Nas demais `a :: as`, colocamos `a :: false :: barCode as` (representando `a0...`).
-/
def barCode : Word → Word
  | []      => []
  | [a]     => [a, true]
  | a :: as => a :: false :: barCode as

/--
Codificação `code(w) = \overline{bin(|w|)} w` (pág. 79, Exercício 9.4):
Recebe uma função `bin` que converte números em binário, e cola `\overline{bin(|w|)}` antes de `w`.
-/
def selfTermCode (bin : ℕ → Word) (w : Word) : Word :=
  barCode (bin w.length) ++ w

end KolmogorovBounds
