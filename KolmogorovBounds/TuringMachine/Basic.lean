namespace TuringMachine.Basic

abbrev Word := List Bool

/-
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

end TuringMachine.Basic
