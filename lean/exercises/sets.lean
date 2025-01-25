import data.set.basic data.set.lattice data.nat.parity
open set nat function
open_locale classical

variables {α : Type*} {β : Type*} {γ : Type*} {I : Type*}

section set_variables

variables (x : α) (A B C : set α)

/-
  # Sets in Lean

  Since Lean is founded on type theory rather than set theory, one must define sets in terms of types.
  In Lean, the type of "sets of terms of type α" is denoted `set α`, and is defined as `α → Prop`.
  That is, a set `X` is really a function `α → Prop`, which sends a term `x : α` to the proposition `x ∈ X`.

  In this way,
    - unions `A ∪ B` are defined as `λ (x : α), A x ∨ B x`
    - intersections `A ∪ B` are defined as `λ (x : α), A x ∧ B x`
    - the empty set `∅` is defined as `λ (x : α), false`
    - the subset relation `A ⊆ B` is defined as `∀ (x : α), A x → B x`
    - et cetera
-/

/-
  # Notation
-/

#check A ⊆ B          -- `\sub`
#check x ∈ A          -- `\in` or `\mem`
#check x ∉ A          -- `\notin`
#check A ∩ B          -- `\i` or `\cap`
#check A ∪ B          -- `\un` or `\cup`
#check (∅ : set α)    -- `\empty`
#check (univ : set α) -- univ, the set containing all terms of α

/-
  # Examples
-/

-- Below are three proofs of the same fact `A ⊆ B → A ∩ C ⊆ B ∩ C`
-- The first two proofs expand definitions explicitly,
-- while the third forces Lean to do the unfolding.

example (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
begin
  rw [subset_def, inter_def, inter_def],
  rw subset_def at h,
  dsimp,
  rintros x ⟨xa, xb⟩,
  exact ⟨h _ xa, xb⟩,
end

example (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  rintros x ⟨xa, xb⟩,
  exact ⟨h _ xa, xb⟩,
end

example (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
begin
  intros x xac,
  exact ⟨h xac.1, xac.2⟩
end

-- Use `cases` or `rcases` or `rintros` with union.
-- Two proofs of the same fact, one longer and one shorter.

example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
begin
  intros x hx,
  have xa : x ∈ A := hx.1,
  have xbc : x ∈ B ∪ C := hx.2,
  cases xbc with xb xc,
  { left,
    show x ∈ A ∩ B,
    exact ⟨xa, xb⟩ },
  right,
  show x ∈ A ∩ C,
  exact ⟨xa, xc⟩
end

example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
begin
  rintros x ⟨xa, xb | xc⟩,
  { left, exact ⟨xa, xb⟩ },
  right, exact ⟨xa, xc⟩
end

-- Two examples with set difference.
-- Type it as `\\`.
-- `x ∈ s \ t` expands to `x ∈ s ∧ x ∉ t`.

example : A \ B \ C ⊆ A \ (B ∪ C) :=
begin
  intros x xabc,
  have xa : x ∈ A := xabc.1.1,
  have xnb : x ∉ B := xabc.1.2,
  have xnc : x ∉ C := xabc.2,
  split,
  { exact xa }, dsimp,
  intro xbc, -- x ∈ t ∨ x ∈ u
  cases xbc with xb xc,
  { show false, from xnb xb },
  show false, from xnc xc
end

example : A \ B \ C ⊆ A \ (B ∪ C) :=
begin
  rintros x ⟨⟨xa, xnb⟩, xnc⟩,
  use xa,
  rintros (xb | xc); contradiction
end

/-
  # Exercises
-/

example : (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C) := sorry

example : A \ (B ∪ C) ⊆ A \ B \ C := sorry

/-
  # Proving two sets are equal
-/

-- To prove two sets are equal, one can use the `ext` tactic.
-- This changes the goal from `A = B` to `x ∈ A ↔ x ∈ B`.

example : A ∩ B = B ∩ A :=
begin
  ext x,
  -- simp only [mem_inter_eq],  -- optional.
  split,
  { rintros ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

example : A ∩ B = B ∩ A :=
by ext x; simp [and.comm]

/-
  # Exercises
-/

example : A ∩ (A ∪ B) = A := sorry

example : A ∪ (A ∩ B) = A := sorry

example : (A \ B) ∪ B = A ∪ B := sorry

example : (A \ B) ∪ (B \ A) = (A ∪ B) \ (A ∩ B) := sorry

/-
  # Set-builder notation

  The set-builder notation can be used to define sets in a way that is more familiar to mathematicians.
-/

def evens : set ℕ := {n | even n}
def odds :  set ℕ := {n | ¬ even n}

/-
  It is equivalent to writing:

  `def evens : set ℕ := λ n, even n`
  `def odds : set ℕ := λ n, ¬ even n`
-/

example : evens ∪ odds = univ :=
begin
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em, -- (law of excluded middle)
end

example : A ∩ B = {x | x ∈ A ∧ x ∈ B} := rfl
example : A ∪ B = {x | x ∈ A ∨ x ∈ B} := rfl
example : (∅ : set α) = {x | false} := rfl
example : (univ : set α) = {x | true} := rfl
example (x : ℕ) (h : x ∈ (∅ : set ℕ)) : false := h
example (x : ℕ) : x ∈ (univ : set ℕ) := trivial

/-
  # Exercise
-/

-- Use `intro n` to unfold the definition of subset,
-- and use the simplifier to reduce the
-- set-theoretic constructions to logic.
-- We also recommend using the theorems
-- `prime.eq_two_or_odd` and `even_iff`.

example : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } := sorry

/-
  # Indexed unions
-/

section

-- Note: we use ℕ as our index type, but this could be any type.
variables X Y : ℕ → set α

example : A ∩ (⋃ i, X i) = ⋃ i, (X i ∩ A) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩ },
  rintros ⟨i, xAi, xs⟩,
  exact ⟨xs, ⟨i, xAi⟩⟩
end

example : (⋂ i, X i ∩ Y i) = (⋂ i, X i) ∩ (⋂ i, Y i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  split,
  { intro h,
    split,
    { intro i,
      exact (h i).1 },
    intro i,
    exact (h i).2 },
  rintros ⟨h1, h2⟩ i,
  split,
  { exact h1 i },
  exact h2 i
end

end

/-
  # Exercise
-/

-- One direction requires classical logic!
-- We recommend using `by_cases xs : x ∈ s`
-- at an appropriate point in the proof.

section

variables X Y : ℕ → set α

example : A ∪ (⋂ i, X i) = ⋂ i, (X i ∪ A) := sorry

end

end set_variables

/-
  # Functions
-/

section function_variables

variable  f : α → β
variables A B : set α
variables C D : set β
variable  X : I → set α
variable  Y : I → set β

#check f '' A
#check image f A
#check f ⁻¹' C    -- type as \inv' and then hit space or tab
#check preimage f C

example : f '' A = {y | ∃ x, x ∈ A ∧ f x = y} := rfl
example : f ⁻¹' C = {x | f x ∈ C } := rfl

example : f ⁻¹' (C ∩ D) = f ⁻¹' C ∩ f ⁻¹' D :=
by { ext, refl }

example : f '' (A ∪ B) = f '' A ∪ f '' B :=
begin
  ext y, split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { left, use [x, xs] },
    right, use [x, xt] },
  rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
  { use [x, or.inl xs] },
  use [x, or.inr xt]
end

example : A ⊆ f ⁻¹' (f '' A) :=
begin
  intros x xs,
  show f x ∈ f '' A,
  use [x, xs]
end

/-
  # Exercises
-/

example : f '' A ⊆ C ↔ A ⊆ f ⁻¹' C := sorry

example (h : injective f) : f ⁻¹' (f '' A) ⊆ A := sorry

example : f '' (f⁻¹' C) ⊆ C := sorry

example (h : surjective f) : C ⊆ f '' (f⁻¹' C) := sorry

example (h : A ⊆ B) : f '' A ⊆ f '' B := sorry

example (h : C ⊆ D) : f ⁻¹' C ⊆ f ⁻¹' D := sorry

example : f ⁻¹' (C ∪ D) = f ⁻¹' C ∪ f ⁻¹' D := sorry

example : f '' (A ∩ B) ⊆ f '' A ∩ f '' B := sorry

example (h : injective f) : f '' A ∩ f '' B ⊆ f '' (A ∩ B) := sorry

example : f '' A \ f '' B ⊆ f '' (A \ B) := sorry

example : f ⁻¹' C \ f ⁻¹' D ⊆ f ⁻¹' (C \ D) := sorry

example : f '' A ∩ D = f '' (A ∩ f ⁻¹' D) := sorry

example : f '' (A ∩ f ⁻¹' C) ⊆ f '' A ∪ C := sorry

example : A ∩ f ⁻¹' C ⊆ f ⁻¹' (f '' A ∩ C) := sorry

example : A ∪ f ⁻¹' C ⊆ f ⁻¹' (f '' A ∪ C) := sorry

example : f '' (⋃ i, X i) = ⋃ i, f '' X i := sorry

example : f '' (⋂ i, X i) ⊆ ⋂ i, f '' X i := sorry

example (i : I) (injf : injective f) : (⋂ i, f '' X i) ⊆ f '' (⋂ i, X i) := sorry

example : f ⁻¹' (⋃ i, Y i) = ⋃ i, f ⁻¹' (Y i) := sorry

example : f ⁻¹' (⋂ i, Y i) = ⋂ i, f ⁻¹' (Y i) := sorry

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  sorry
  -- Suppose f : α → set α is a surjective function.
  -- Let S = { x | x ∉ f x }.
  -- Because f is surjective, there is some x : α such that f x = S.
  -- We will now show that x ∉ f x, which will be a contradiction.
  --   Suppose x ∈ f x.
  --   Since f x = S, we have x ∈ S.
  --   Hence x ∉ f x.
  -- Since x ∉ f x and f x = S, we have x ∉ S.
  -- Since x ∉ f x, we have x ∈ S.
  -- Contradiction.
end

end function_variables
