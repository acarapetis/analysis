import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.2: Russell's paradox

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

This section is mostly optional, though it does make explicit the axiom of foundation which is
used in a minor role in an exercise in Section 3.5.

Main constructions and results of this section:

- Russell's paradox (ruling out the axiom of universal specification).
- The axiom of regularity (foundation) - an axiom designed to avoid Russell's paradox.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (Universal specification) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- This proof is written to follow the structure of the original text.
  intro h
  set P : Object → Prop := fun x ↦ ∃ X:Set, x = X ∧ x ∉ X
  choose Ω hΩ using h P
  by_cases h: (Ω:Object) ∈ Ω
  . have : P (Ω:Object) := (hΩ _).mp h
    obtain ⟨ Ω', ⟨ hΩ1, hΩ2⟩ ⟩ := this
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    contradiction
  have : P (Ω:Object) := by use Ω
  rw [←hΩ] at this
  contradiction

/-- Axiom 3.9 (Regularity) -/
theorem SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x:A, ∀ S:Set, x.val = S → Disjoint S A := by
  choose x h h' using regularity_axiom A (nonempty_def h)
  use ⟨x, h⟩
  intro S hS; specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'; simp at h'
  aesop

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h: axiom_of_universal_specification):
    ∃ (X:Set), ∀ x, x ∉ X := by
  simpa using h (fun y => False)

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h: axiom_of_universal_specification) (x:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x := by
  simpa using h (fun y => y = x)

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h: axiom_of_universal_specification) (x₁ x₂:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  simpa using h (fun y => y = x₁ ∨ y = x₂)

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h: axiom_of_universal_specification) (A B:Set):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  simpa using h (fun y => y ∈ A ∨ y ∈ B)

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h: axiom_of_universal_specification) (A:Set) (P: A → Prop):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  simpa using h (fun z => ∃ h: z ∈ A, P ⟨z, h⟩)

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the replace operation.
-/
theorem SetTheory.Set.replace_exists (h: axiom_of_universal_specification) (A:Set)
  (P: A → Object → Prop) (hP: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z:Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  simpa using h (fun y => ∃ a : A, P a y)

lemma SetTheory.Set.insert_not_empty (x: Object) (X: Set): insert x X ≠ ∅ := by
  apply nonempty_of_inhabited (X:=insert x X) (x:=x)
  simp_all

lemma SetTheory.Set.sing_not_empty (x: Object): ({x}: Set) ≠ ∅ := by
  have hx : x ∈ ({x}: Set) := by simp_all
  by_contra h
  rw [h] at hx
  simp_all

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A:Set) : (A:Object) ∉ A := by
  have h2: set_to_object A ∈ ({set_to_object A}:Set) := by simp_all
  have hnz: {set_to_object A} ≠ (∅: Set) := sing_not_empty A
  have h' := axiom_of_regularity (A := {set_to_object A}) hnz
  simp_all
  rw [disjoint_iff] at h'
  have hem := emptyset_mem A
  change set_to_object A ∉ (∅:Set) at hem
  rw [<-h',mem_inter] at hem
  simp_all

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:Object) ∉ B ∨ (B:Object) ∉ A := by
  let AB: Set := {(A:Object), (B:Object)}
  have hAB: AB ≠ ∅ := insert_not_empty A {(B:Object)}
  obtain ⟨x, hx⟩ := axiom_of_regularity hAB
  have hcases: x.val = (A:Object) ∨ x.val = (B:Object) := by
    have hap := x.prop
    rw [mem_pair] at hap
    simp_all
  obtain hA|hB := hcases
  . have h2 := hx A hA
    rw [disjoint_iff] at h2
    have : (B:Object) ∉ A := by
      by_contra h
      have : (B: Object) ∈ AB := by grind [mem_pair]
      have : (B: Object) ∈ A ∩ AB := by grind [mem_inter]
      have : A ∩ AB ≠ ∅ := by simp_all
      contradiction
    simp_all
  . have h2 := hx B hB
    rw [disjoint_iff] at h2
    have : (A:Object) ∉ B := by
      by_contra h
      have : (A: Object) ∈ AB := by grind [mem_pair]
      have : (A: Object) ∈ B ∩ AB := by grind [mem_inter]
      have : B ∩ AB ≠ ∅ := by simp_all
      contradiction
    simp_all

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
    ∃ (U:Set), ∀ x, x ∈ U := by
  constructor
  . intro h
    have := h (fun x => True)
    simp_all
  . intro ⟨U, hU⟩ P
    use specify U (fun x => P x.val)
    simp_all

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := by
  rw [<-univ_iff]
  exact Russells_paradox

end Chapter3
