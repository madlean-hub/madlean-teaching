import Mathlib.Tactic

/-!
# Lógica proposicional

Resuelve los siguientes ejercicios utilizando solo las tácticas
* `intro`
* `apply`
* `exact`
* `by_contra`
-/

example (P : Prop) : P → P := by
  intro hP
  exact hP

example (P Q : Prop) (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP
  -- or `exact h hP`

example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) : P → R := by
  intro hP
  apply h2
  apply h1
  exact hP

-- Nota: recuerda que `¬P` para Lean es lo mismo que `P → False`

lemma contrarreciproco (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  intro hNQ hP
  apply hNQ
  apply h
  exact hP

-- Si no lo has conseguido ya, intenta resolver el ejercicio anterior sin utilizar `by_contra`

lemma P_implica_nonoP (P : Prop) : P → ¬¬P := by
  intro hp hnp
  apply hnp
  exact hp

lemma nonoP_implica_P (P : Prop) : ¬¬P → P := by
  intro hp
  by_contra hc
  apply hp
  exact hc

lemma contrarreciproco' (P Q : Prop) (h : ¬P → ¬Q) : Q → P := by
  intro hQ
  by_contra hP
  --change (P → False) → Q → False at h
  apply h -- Reflexiona: ¿por qué esto genera 2 goals?
  · exact hP
  · exact hQ


/-!
# Reutilizando resultados

Resuelve los siguientes ejercicios utilizando solo las tácticas
* `constructor`
* `intro`
* `exact`

Para ello, deberás utilizar los resultados que demostraste en el apartado anterior.

Nota: cuando trabajes con dos hipótesis, recuerda utilizar `·`.
-/

variable (P Q : Prop)

lemma P_iff_nonoP : P ↔ ¬¬ P := by
  constructor
  · exact P_implica_nonoP P
  · exact nonoP_implica_P P

example : (P → Q) ↔ (¬Q → ¬P) := by
  constructor
  all_goals intro h -- ¿Qué crees que hace la táctica `all_goals`?
  · exact contrarreciproco P Q h
  · exact contrarreciproco' Q P h

/-!
# Propiedades sobre funciones
-/

-- Esta es la definición de Mathlib de función inyectiva:
#check Function.Injective
#print Function.Injective

-- Si abrimos el namespace `Function`, no hace falta que escribamos `Function.Injective` cada vez:

open Function
#check Injective

-- Podemos escribir nuestra propia versión de inyectividad:

def inyectiva {X Y : Type} (f : X → Y) : Prop :=
  ∀ x y : X, f x = f y → x = y

-- Compara las definiciones y anota tus dudas para la próxima vez :)

#print Function.Injective
#print inyectiva

/-!
## Escribe tus propias definiciones

Ejercicio: escribe tu propia definición de función `sobreyectiva` y `biyectiva`.
-/

variable {X Y : Type} (f : X → Y)

def sobreyectiva : Prop := ∀ y : Y, ∃ x : X, f x = y

def biyectiva : Prop := inyectiva f ∧ sobreyectiva f

/-!
## La función identidad

Aparte de las tácticas que hemos usado hasta ahora, utilizaremos `use` y `rfl`:

antes             | táctica  | después
------------------|----------|--------------
`y : X`           |          |
`⊢ ∃ x : X, P x`  | `use y`  | `⊢ P y`
------------------|----------|--------------
`⊢ x = x`         | `rfl`    | `No goals!`

Cuando queremos demostrar un existe, utilizamos `use` para especificar el objeto concreto que
vamos a usar para demostrar el existe.

Utilizamos `rfl` (de propiedad reflexiva) cuando el goal es una igualdad (u otra relación de
equivalencia) entre dos cosas que son iguales (o iguales por definición).
-/

-- Ejemplos de estas dos tácticas:

example : 1 = 1 := by
  rfl

example : ∃ x : ℕ, x = 1 := by
  use 1

/-!
Considera la siguiente definición de función identidad y demuestra que es inyectiva, sobreyectiva
y biyectiva.

Nota: para facilitarte la vida, puedes utilizar la táctica `unfold`.
Nota: si quieres, puedes utilizar tus propias definiciones!
-/

def identidad (X : Type) : X → X := fun x ↦ x

variable (X : Type)

lemma identidad_inyectiva : Injective (identidad X) := by
  --unfold Injective
  intro x y h
  --unfold identidad at h
  exact h

lemma identidad_sobreyectiva : Surjective (identidad X) := by
  intro x
  use x
  rfl

lemma identidad_biyectiva : Bijective (identidad X) := by
  constructor
  · exact identidad_inyectiva X -- Reflexiona: ¿por qué tenemos que poner `X` aquí?
  · exact identidad_sobreyectiva _ -- ¿Qué crees que hace aquí poner `_`?


/-!
## Composición de funciones

Demostramos que dadas dos funciones inyectivas (respectivamente sobreyectivas y biyectivas),
la composición de ambas es inyectiva (respectivamente sobreyectiva y biyectiva)

Nota: es lo mismo `Injective f` que `f.Injective`.
Nota: para ayudarte a entender lo que haces, utiliza `unfold comp` (deshace la definición de
composición)

Necesitarás las tácticas adicionales `specialize`, `obtain` y `rw`:

antes              | táctica               | después
-------------------|-----------------------|--------------
`h : ∀ x : X, P x` |                       | `y : X`
`y : X`            | `specialize h y`      | `h : P y`
-------------------|-----------------------|--------------
`h : P → Q`        |                       | `hP : P`
`hP : P`           | `specialize h hP`     | `h : Q`
-------------------|-----------------------|--------------
`h : ∃ x : X, P x` | `obtain ⟨x, hx⟩ := h` | `x : X`
-                  |                       | `hx : P x`
-------------------|-----------------------|--------------
`h : x = y`        |                       |
`⊢ P x`            | `rw [h]`              | `⊢ P y`
-------------------|-----------------------|--------------
`h : P ↔ Q`        |                       |
`⊢ P`              | `rw [h]`              | `⊢ Q`


* Utilizamos `specialize` táctica cuando tenemos una hipótesis de tipo "para todo". Si se cumple
para todo x, entonces se cumple para uno concreto. Queremos elegir ese elemento concreto.

* También lo utilizamos de forma parecida a `apply`. ¿Puedes encontrar la diferencia?

* Utilizamos `obtain` para deshacer una hipótesis existencial. Si sabemos que existe un cierto
`x` que cumple `P x`, podemos decir "sea `x` tal que `P x`".

* Utilizamos `rw` para intercambiar objetos que están realcionados mediante una relación
de equivalencia, por ejemplo igualdad o doble implicación.
-/


-- Ejemplos de estas tácticas

example (h : ∀ n : ℕ, n ≥ 0) : 3 ≥ 0 := by
  specialize h 3
  exact h

example (h : P → Q) (hP : P) : Q := by
  specialize h hP
  exact h

example (h3 : 3 > 1) (h : ∀ n : ℕ, n > 1 → n > 0) : 3 > 0 := by
  specialize h 3 h3
  exact h

example (h : ∃ x : ℝ, x > 0) : ∃ x : ℝ, (identidad ℝ) x > 0 := by
  obtain ⟨x, hx⟩ := h
  use x
  exact hx

example (x y : ℝ) (h1 : x = 3) (h2 : x = y) : y = 3 := by
  rw [← h1]
  rw [h2]

example (h : P ↔ Q) (hQ : Q) : P := by
  rw [h]
  exact hQ

example (h : P ↔ Q) (hP : P) : Q := by
  rw [← h]
  exact hP

variable {X Y Z : Type}

lemma composicion_inyectiva (f : X → Y) (g : Y → Z) (hf : f.Injective) (hg : g.Injective) :
    (g ∘ f).Injective := by
  intro x y h
  --unfold comp at h
  --unfold Injective at hf hg
  apply hg at h
  apply hf at h
  exact h

lemma composicion_sobreyectiva (f : X → Y) (g : Y → Z) (hf : f.Surjective) (hg : g.Surjective) :
    (g ∘ f).Surjective := by
  intro z
  specialize hg z
  obtain ⟨y, hy⟩ := hg
  specialize hf y
  obtain ⟨x, hx⟩ := hf
  use x
  unfold comp
  rw [hx]
  rw [hy]

-- Utiliza los dos resultados anteriores para demostrar este último resultado:
lemma composicion_biyectiva (f : X → Y) (g : Y → Z) (hf : f.Bijective) (hg : g.Bijective) :
    (g ∘ f).Bijective := by
  constructor
  · exact composicion_inyectiva f g hf.1 hg.1
  · exact composicion_sobreyectiva f g hf.2 hg.2
