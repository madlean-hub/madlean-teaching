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
  sorry

example (P Q : Prop) (h : P → Q) (hP : P) : Q := by
  sorry

example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) : P → R := by
  sorry

-- Nota: recuerda que `¬P` para Lean es lo mismo que `P → False`

lemma contrarreciproco (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  sorry

-- Si no lo has conseguido ya, intenta resolver el ejercicio anterior sin utilizar `by_contra`

lemma P_implica_nonoP (P : Prop) : P → ¬¬P := by
  sorry

lemma nonoP_implica_P (P : Prop) : ¬¬P → P := by
  sorry

lemma contrarreciproco' (P Q : Prop) (h : ¬P → ¬Q) : Q → P := by
  sorry


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
  sorry

example : (P → Q) ↔ (¬Q → ¬P) := by
  sorry

/-!
  # Disyunciones
  El tipo `P ∨ Q` se construye con dos reglas de introducción:

  * `Or.inl : P → P ∨ Q`  -> si tienes una prueba de `P`, obtienes `P ∨ Q`
  * `Or.inr : Q → P ∨ Q`  -> si tienes una prueba de `Q`, obtienes `P ∨ Q`

  En modo táctico, las tácticas `left` y `right` aplican `Or.inl` y `Or.inr` respectivamente.

  * `left`
  * `right`

  Para razonar sobre una disyunción, necesitamos probar sobre cada uno de los casos.
  Para ello podemos usar la táctica rcases

  * `rcases poq : (P ∨ Q) with p | q`

-/

example : P → (P ∨ Q) := by
  sorry

example : (P ∨ Q) → (Q ∨ P) := by
  sorry

/-!
  # Conjunciones
  El tipo `P ∧ Q` se construye con una regla de introducción:

  * `And.intro : P → Q → P ∧ Q`  -> si tienes pruebas de `P` y de `Q`, obtienes `P ∧ Q`

  En modo táctico, la táctica `constructor` divide el goal `P ∧ Q` en dos subgoals: `⊢ P` y `⊢ Q`.

  * `constructor`

  Para razonar sobre una conjunción, podemos acceder a cada componente con los accesores:

  * `h.1 : P`  — si `h : P ∧ Q`, obtienes la prueba de `P`
  * `h.2 : Q`  — si `h : P ∧ Q`, obtienes la prueba de `Q`

-/

example : P ∧ Q → P := by
  sorry

example : Q ∧ P → P ∧ Q := by
  sorry

/-!
# Algunos resultados sobre lógica proposicional interesantes
-/

lemma dne_implica_lem : (∀ P, (¬¬P → P)) → (∀ Q, (Q ∨ ¬Q)) := by
  sorry

lemma lem_implica_dne : (∀ Q, (Q ∨ ¬Q)) → (∀ P, (¬¬P → P)) := by
  sorry
