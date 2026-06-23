import Mathlib.Tactic
import Mathlib.Order.SymmDiff

/-
Lista de tácticas que tenemos hasta ahora:
* `intro`
* `apply`
* `exact`
* `exfalso`
* `by_contra`
* `constructor`
* `left`
* `right`
* `rcases` `with`
* `contradiction`
* `use`
* `rfl`
* `specialize`
* `obtain`
* `rw`
* `unfold`

Nuevas tácticas:
* `norm_num`
* `linarith`
* `exact?`
to-do: añadir explicación y tabla
-/

/-!
# El tipo `Set X`

En Lean 4 (y Mathlib), Set X representa el tipo de los conjuntos de elementos de tipo X.
Formalmente:

`def Set (X : Type*) : Type* := X → Prop`

Un Set X es simplemente una función de X a Prop: dado un elemento x : X, el conjunto te dice si x
pertenece a él o no. Es decir, un conjunto es su función característica.
-/

variable {X : Type}
#check Set X

/-!
## Pertenencia

Dado `s : Set X` (un conjunto) y `x : X` un elemento de tipo X, la notación `x ∈ s`
(escribimos ∈ como `\in`) es la proposición de que `x` pertenece a `s` (es decir,
x satisface la proposición que define al conjunto).

Nota: `y ∈ {x | P x}` =(def) `P y`

Por ejemplo:
-/

def mi_conjunto : Set ℝ := {x | x > 0}

example : 3 ∈ mi_conjunto := by
  unfold mi_conjunto
  norm_num

example : -1 ∉ mi_conjunto := by -- escribe ∉ usando `\notin`
  unfold mi_conjunto
  norm_num

-- Ejercicio: escribe el conjunto de los números pares y el de los números impares
def pares : Set ℕ := {n | ∃ m, n = 2 * m}
def impares : Set ℕ := {n | ∃ m, n = 2 * m + 1}

-- Ejercicio:
example : 4 ∈ pares := by
  use 2

example : 4 ∉ impares := by
  intro h
  obtain ⟨n, hn⟩ := h
  -- completar
  sorry


/-!
## Subset

A ⊆ B == ∀ {a}, a ∈ A → a ∈ B
-/

variable (A B C : Set X) -- sean A, B y C conjuntos arbitrarios
variable (x y : X)

example (h : A ⊆ B) (hx : x ∈ A) : x ∈ B := by
  --specialize h (a:=x) -- no es necesario porque `apply h` infiere el argumento `a`
  apply h
  exact hx

lemma my_subset_trans (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro a ha
  apply h2
  apply h1
  exact ha

example : {x : ℝ | x > 0} ⊆ {x : ℝ | x ≥ 0} := by
  intro x hx
  rw [Set.mem_setOf_eq] at ⊢ hx
  linarith

/-!
## Unión e intersección

`x ∈ A ∩ B` =(def) `x ∈ A ∧ x ∈ B`

`x ∈ A ∪ B` =(def) `x ∈ A ∨ x ∈ B`

Ejercicios:
-/

example (hx : x ∈ A ∩ B) : x ∈ A := by
  exact hx.1

example (hx : x ∈ A ∪ B) (hx' : x ∉ A) : x ∈ B := by sorry


lemma inter_comm : A ∩ B = B ∩ A := by
  sorry

lemma union_comm : A ∪ B = B ∪ A := by
  sorry

example : A ⊆ A ∪ B := by sorry

example : A ∩ B ⊆ B := by sorry

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by sorry

/-!
## Complementario

`Aᶜ` = `∀ {x}, x ∈ A → False`

Para escribir ᶜ utiliza `\compl`
-/

example (hx : x ∉ A) : x ∈ Aᶜ := by
  intro hx'
  exact hx hx'

example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  exact Set.compl_union A B

example : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by sorry

example : Aᶜᶜ = A := by sorry

example (h : A ⊆ B) : Bᶜ ⊆ Aᶜ := by sorry


/-
Una vez los hayas demostrado normalmente, también intenta:
1. utilizando `exact?`
2. utilizando leansearch, moogle o loogle
-/


/-
Teoría: `structure`

Ejercicios:
* Definir una estructura de grupo / una topología
* Demostrar que los enteros con la suma son un grupo
* Ejercicios para casa: otras instancias de grupos
* Ejercicio para casa: definir otra estructura ¿Cuál?
-/

/-!
## Estructuras (`structure`)

Una `structure` en Lean es una forma de agrupar varios datos bajo un mismo nombre.
Es el equivalente a un "registro" o "struct": defines qué campos tiene, y luego
puedes construir valores dando un valor para cada campo.

Por ejemplo, un número complejo tiene parte real e imaginaria:
-/

structure Complejo where
  re : ℝ
  im : ℝ

-- Para construir un valor de tipo Complejo, damos sus campos:
def z : Complejo := { re := (3 : ℝ), im := -1 }

-- Accedemos a los campos con la notación punto:
#check z.re  -- ℝ
#check z.im  -- ℝ

structure miGrupo (X : Type) where
  G : Set X
  op : X → X → X -- mirar como se hace para poner `x op y`
  op_cerrada : ∀ x ∈ G, ∀ y ∈ G, op x y ∈ G
  op_assoc : ∀ x ∈ G, ∀ y ∈ G, ∀ z ∈ G, op x (op y z) = op (op x y) z
  e : X
  op_neutro : ∀ x ∈ G, op e x = x ∧ op x e = x
  op_inv : ∀ x ∈ G, ∃ y ∈ G, op x y = e ∧ op y x = e

def enteros_con_suma : miGrupo ℤ where
  G := Set.univ
  e := 0
  op := fun x => fun y => x + y
  op_cerrada := by
    intros
    trivial -- `x ∈ Set.univ == True`
  op_assoc := by
    intro x hx y hy z hz
    exact Eq.symm (Int.add_assoc x y z) -- exact?
  op_neutro := by
    intro x hx
    exact ⟨Int.zero_add x, Int.add_zero x⟩ --- exact? x2
  op_inv := by
    intro x hx
    use -x
    constructor
    · trivial
    constructor
    · exact Int.add_right_neg x -- exact?
    · exact Int.add_left_neg x -- exact?

#check enteros_con_suma.op

/-
grupo de conjuntos con la operación Diferencia simétrica?
-/

variable (X : Type)

def conjuntos_con_diferencia_simetrica : miGrupo (Set X) where
  G := Set.univ
  e := ∅
  op := symmDiff
  op_cerrada := sorry
  op_assoc := sorry
  op_neutro := sorry
  op_inv := sorry


/-!
## Subgrupos

Dado un grupo `G`, decimos que un subconjunto `H ⊆ G` es un subgrupo si es cerrado bajo
la operación y los inversos, y contiene al neutro.

Ejercicios:
* Define una estructura `miSubgrupo`.
* Demuestra que si `H` tiene estructura de subgrupo entonces tiene estructura de grupo.
-/

structure miSubgrupo (X : Type) (G : miGrupo X) where
  H : Set X
  H_sub : H ⊆ G.G
  e_mem : G.e ∈ H
  op_cerrada : ∀ x ∈ H, ∀ y ∈ H, G.op x y ∈ H
  inv_cerrada : ∀ x ∈ H, ∃ y ∈ H, G.op x y = G.e ∧ G.op y x = G.e

-- Ejercicio: demuestra que todo subgrupo es un grupo
example (X : Type) (G : miGrupo X) (S : miSubgrupo X G) : miGrupo X where
  G := S.H
  e := G.e
  op := G.op
  op_cerrada := S.op_cerrada
  op_neutro := by
    intro x hx
    exact G.op_neutro x (S.H_sub hx)
  op_inv := by
    intro x hx
    obtain ⟨y, hy_H, hy⟩ := S.inv_cerrada x hx
    exact ⟨y, hy_H, hy⟩
  op_assoc := by
    intro x hx y hy z hz
    exact G.op_assoc x (S.H_sub hx) y (S.H_sub hy) z (S.H_sub hz)
