import Mathlib.Tactic

variable (P Q : Prop)

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

--def sobreyectiva ...


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
  sorry

lemma identidad_sobreyectiva : Surjective (identidad X) := by
  sorry

lemma identidad_biyectiva : Bijective (identidad X) := by
  sorry


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
`h : x = y`        |                       |
`⊢ P y`            | `rw [← h]`            | `⊢ P x`
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
  sorry

lemma composicion_sobreyectiva (f : X → Y) (g : Y → Z) (hf : f.Surjective) (hg : g.Surjective) :
    (g ∘ f).Surjective := by
  sorry

-- Utiliza los dos resultados anteriores para demostrar este último resultado:
lemma composicion_biyectiva (f : X → Y) (g : Y → Z) (hf : f.Bijective) (hg : g.Bijective) :
    (g ∘ f).Bijective := by
  sorry

/-!
## Función inversa

Intenta dar las siguientes definiciones

-/

def InversaIzquierda (f : X → Y) (g : Y → X) : Prop := sorry
def InversaDerecha (f : X → Y) (g : Y → X) : Prop := sorry
def Inversa (f : X → Y) (g : Y → X) : Prop := sorry

variable {f : X → Y} {g : Y → X}

lemma inv_izqd_drch : InversaIzquierda f g ↔ InversaDerecha g f := by
  sorry

def TieneInversaIzquierda (f : X → Y) : Prop := sorry
def TieneInversaDerecha (f : X → Y) : Prop := sorry
def TieneInversa (f : X → Y) : Prop := sorry

example : TieneInversa (identidad X) := by
  sorry

noncomputable def invSurj (f : X → Y) (hf : Surjective f) : Y → X := sorry
  -- fun b => Classical.choose (hf b)

theorem invSurj_invizquierda (h : Surjective f) : InversaIzquierda f (invSurj f h) := sorry
  --fun b => Classical.choose_spec (h b)

lemma biyectiva_iff_TieneInversa : Bijective f ↔ TieneInversa f := by
  sorry
