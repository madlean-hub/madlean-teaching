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
* `assumption`
* `use`
* `rfl`
* `specialize`
* `obtain`
* `rw`
* `unfold`
-/

/-!
# Nuevas tácticas


## norm_num

La táctica `norm_num` cierra goals que son afirmaciones numéricas concretas y calculables.

Por ejemplo:
-/

example : 2 + 2 = 4 := by norm_num
example : (7 : ℝ) / 2 > 3 := by norm_num
example : ¬ (5 : ℤ) ∣ 17 := by norm_num

/-
Sin embargo, `norm_num` necesita que los números sean literales o expresiones cerradas,
sin variables:
-/

example (x : ℝ) (hx : x > 0) : x + 2 > 2 := by
  norm_num -- norm_num consigue que la hipótesis ahora sea x > 0
  -- pero no la cierra porque no puede trabajar sobre variables
  assumption

/-
## Linarith

En el caso en el que tengamos variables en goals con desigualdades lineales, podemos utilizar la
táctica `linarith`.

Por ejemplo:
-/

example (x : ℝ) (hx : x > 0) : x + 2 > 2 := by linarith
example (x y : ℝ) (h1 : 2 * x + y ≤ 10) (h3 : y ≥ 0) : x ≤ 5 := by linarith

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
  sorry

-- Ejercicio: escribe el conjunto de los números pares y el de los números impares
def pares : sorry := sorry
def impares : sorry := sorry

-- Ejercicio:
--example : 4 ∈ pares := by

--example : 4 ∉ impares := by

/-!
## Subset

A ⊆ B == ∀ {a}, a ∈ A → a ∈ B
-/

variable (A B C : Set X) -- sean A, B y C conjuntos arbitrarios
variable (x y : X)

example (h : A ⊆ B) (hx : x ∈ A) : x ∈ B := by
  sorry

lemma my_subset_trans (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  sorry

example : {x : ℝ | x > 0} ⊆ {x : ℝ | x ≥ 0} := by
  sorry

/-!
## Unión e intersección

`x ∈ A ∩ B` =(def) `x ∈ A ∧ x ∈ B`

`x ∈ A ∪ B` =(def) `x ∈ A ∨ x ∈ B`

Ejercicios:
-/

example (hx : x ∈ A ∩ B) : x ∈ A := by
  sorry

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
  sorry

example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  sorry

example : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by sorry

example : Aᶜᶜ = A := by sorry

example (h : A ⊆ B) : Bᶜ ⊆ Aᶜ := by sorry


/-
# Reutilizar MathLib

Estos ejercicios son interesantes para practicar Lean, porque te
ayudan a familiarizarte con definiciones, igualdad por definición,
tácticas que hemos aprendido... etc.

Pero, en la práctica, si tuvieras que demostrar este tipo de cosas
siempre, no sería muy útil tener tantas líneas de código.

## exact?

A partir de ahora queremos reutilizar resultados de Mathlib
frecuentemente. Existen algunas tácticas que nos ayudan a hacer esto.

La más útil es `exact?`, que busca en Mathlib un lema que cierre el goal actual.

Después puedes pulsar en "aplicar" y te resolverá el ejercicio.

Intenta resolver los ejercicios anteriores de nuevo, utilizando `exact?`.

## Otras herramientas

leansearch, moogle o loogle - to-do
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

def enteros_con_suma : miGrupo ℤ := sorry

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

-- structure miSubgrupo (X : Type) (G : miGrupo X) where

-- Ejercicio: demuestra que todo subgrupo es un grupo
