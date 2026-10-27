import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log

namespace KolmogorovBounds

/-!
# Bloco 1: Strings Binárias e Complexidade de Kolmogorov (A Base Comum)
No texto, tudo é transformado em strings de 0s e 1s (`Word`).
No Lean, representamos uma string binária simplesmente como uma lista de booleanos (`List Bool`).
-/

/-- Uma palavra binária (sequência de 0s e 1s) é uma lista de booleanos. -/
abbrev Word := List Bool

/-- O tamanho `|w|` de uma palavra é o comprimento da lista. -/
def wordLen (w : Word) : ℕ := w.length

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

/-- Versão numérica (pág. 77, Nota de rodapé 1):
O texto simplifica `|bin(n)| = log n`. Aqui dizemos que um número `n` (com tamanho `log_n`)
é incompressível se sua complexidade `K_n` satisfaz `K_n ≥ log_n`. -/
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


/-!
# Bloco 3: Ferramentas do Escopo 2 (Computacional / Máquina de Turing e Crossing Sequences)
Nas páginas 80 a 82 (Exercícios 9.9 a 9.15), analisamos uma Máquina de Turing `M` de 1 fita
através das suas Sequências de Cruzamento (`CS_M(x, i)`).

Para não precisarmos simular fita infinita passo a passo, modelamos a máquina de forma
modular exatamente como os Exercícios 9.10 e 9.12 enxergam a computação:
dividida por uma fronteira `i` entre uma metade esquerda (`x`, de tamanho `i`) e uma metade direita (`y`).
-/

/--
Estrutura abstrata de uma Máquina de Turing com Sequências de Cruzamento (`CS`).
Aqui `State` é o conjunto `Z` de estados da máquina.
-/
structure CrossingTM (State : Type) where
  /-- `CS x y` representa a sequência de cruzamento `CS_M(xy, |x|)` na fronteira exata entre `x` e `y`. -/
  CS : Word → Word → List State
  /-- Indica se a máquina aceita a palavra concatenada `xy` (`xy ∈ L(M)`). -/
  accepts : Word → Word → Prop

  /-- Propriedade de Localidade para o Exercício 9.10 (e WLOG do 9.11):
  Como a máquina para na célula 0 (lado esquerdo), o veredito final de aceitação sobre `xy`
  depende EXCLUSIVAMENTE do que está escrito na esquerda (`x`) e da sequência de estados
  que cruzaram a fronteira (`CS x y`). -/
  accept_depends_on_left : Word → List State → Prop
  accept_iff_left : ∀ x y, accepts x y ↔ accept_depends_on_left x (CS x y)

  /-- Propriedade de Consistência Local para o Exercício 9.12 (Cut-and-Paste):
  Uma sequência `c` é a sequência de cruzamento entre `x` e `y` se e somente se
  `x` é compatível com `c` pela esquerda e `y` é compatível com `c` pela direita. -/
  LeftConsistent : Word → List State → Prop
  RightConsistent : Word → List State → Prop
  cs_eq_iff : ∀ x y c, CS x y = c ↔ (LeftConsistent x c ∧ RightConsistent y c)

/--
Definição da Linguagem `L = { w 0^|w| w | w ∈ {0,1}* }` (pág. 80).
Quando cortamos a palavra `w 0^|w| w` em uma posição `i` no meio dos zeros (`|w| ≤ i ≤ 2|w|`),
o lado esquerdo tem `w` seguido de alguns zeros, e o lado direito tem o resto dos zeros seguido de `w`.
Simplificando na fronteira: a máquina aceita a colagem da metade esquerda de `w` com a metade direita de `w'`
se e somente se `w = w'`!
-/
def RecognizesLanguageL {State : Type} (M : CrossingTM State)
    (leftPart rightPart : Word → Word) : Prop :=
  ∀ w w' : Word, w.length = w'.length →
    (M.accepts (leftPart w) (rightPart w') ↔ w = w')

end KolmogorovBounds
