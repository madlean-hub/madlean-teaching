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
  # Disyunciones
  El tipo `P ∨ Q` se construye con dos reglas de introducción:

  * `Or.inl : P → P ∨ Q`  — si tienes una prueba de `P`, obtienes `P ∨ Q`
  * `Or.inr : Q → P ∨ Q`  — si tienes una prueba de `Q`, obtienes `P ∨ Q`

  En modo táctico, las tácticas `left` y `right` aplican `Or.inl` y `Or.inr` respectivamente.

  * `left`
  * `right`

  Para razonar sobre una disyunción, necesitamos probar sobre cada uno de los casos.
  Para ello podemos usar la tactica rcases

  * `rcases poq : (P ∨ Q) with p | q`

-/

example : P → (P ∨ Q) := by
  intro a
  left
  exact a

example : (P ∨ Q) → (Q ∨ P) := by
  intro poq
  rcases poq with p | q
  · right
    exact p
  · left
    exact q

/-!
# Algunos resultados sobre lógica proposicional interesantes
-/

lemma dne_implica_lem : (∀ P, (¬¬P → P)) → (∀ Q, (Q ∨ ¬Q)) := by
  intro dne q
  apply dne (q ∨ ¬q)
  intro h1
  have nq: ¬q := by
    intro q
    exact h1 (Or.inl q)
  exact h1 (Or.inr nq)

lemma lem_implica_dne : (∀ Q, (Q ∨ ¬Q)) → (∀ P, (¬¬P → P)) := by
  intro lem p np
  have ponp : p ∨ ¬p := lem p
  rcases ponp with p1 | np1
  · exact p1
  · have l: False := np np1
    exact False.elim l
