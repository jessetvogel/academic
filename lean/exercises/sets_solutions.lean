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

example : (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C) := 
begin
  intros x hx, split; cases hx, {
    exact hx.1,
  }, {
    exact hx.1,
  }, {
    left,
    exact hx.2,
  }, {
    right,
    exact hx.2,
  }
end

example : A \ (B ∪ C) ⊆ A \ B \ C := 
begin
  intros x hx,
  split, split, {
    exact mem_of_mem_diff hx,
  }, {
    intro hB,
    apply (not_mem_of_mem_diff hx),
    left,
    exact hB,
  }, {
    intro hA,
    apply (not_mem_of_mem_diff hx),
    right,
    exact hA,
  }
end

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


example : A ∩ (A ∪ B) = A := begin 
  ext x, split; intro h, {
    exact h.1, 
  },{
    split,
    exact h,
    left,
    exact h,
  }
end

example : A ∪ (A ∩ B) = A := begin
  ext x, split; intro h, {
    cases h, {
      exact h,
    }, {
      exact h.1,
    }
  }, {
    left,
    exact h,
  }
end

example : (A \ B) ∪ B = A ∪ B := begin
  ext x, split; intro h, {
    cases h, {
      left,
      exact mem_of_mem_diff h,
    }, {
      right,
      exact h,
    }
  }, {
    by_cases h' : x ∈ B, {
      right,
      exact h',
    }, {
      cases h, {
        left,
        exact mem_sep h h',
      }, {
        exfalso,
        exact h' h,
      }
    }
  }
end

example : (A \ B) ∪ (B \ A) = (A ∪ B) \ (A ∩ B) := begin
  ext, split; intro h, { 
    wlog h' : x ∈ A \ B using A B, {
      exact h,
    },
    split, {
      left,
      exact mem_of_mem_diff h',
    }, {
      intro hx,
      apply not_mem_of_mem_diff h',
      exact hx.2,
    }
  }, {
    have h' := mem_of_mem_diff h,
    cases h', {
      left, split, {
        exact h',
      }, {
        intro hB,
        apply not_mem_of_mem_diff h,
        exact ⟨h',hB⟩,
      }
    }, {
      right, split, {
        exact h',
      }, {
        intro hA,
        apply not_mem_of_mem_diff h,
        exact ⟨hA,h'⟩,
      }
    },
  }
end

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

example : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } := 
begin
  intro n,
  simp,
  intros h1 h2,
  rw even_iff,
  cases prime.eq_two_or_odd h1, {
    exfalso,
    rw h at h2,
    exact lt_asymm h2 h2,
  }, {
    exact mod_two_ne_zero.mpr h,
  }
end

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

example : A ∪ (⋂ i, X i) = ⋂ i, (X i ∪ A) := begin
  ext,split; intro h, 
  {
    rw mem_Inter; intro i,
    cases h, {
      right,
      exact h,
    }, {
      left,
      rw mem_Inter at h,
      exact h i,
    }
  }, {
    by_cases xs : x ∈ A, {
      left,
      exact xs,
    }, {
      right,
      rw mem_Inter at *,
      intro i,
      specialize h i,
      cases h, {
        exact h,
      }, {
        contradiction,
      }
    }
  }
end

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

lemma im_subset_iff_subset_inv : f '' A ⊆ C ↔ A ⊆ f ⁻¹' C := begin
  split; intro h, {
    intros x hx,
    change f x ∈ C,
    have hf : f x ∈ f '' A, use x, exact ⟨ hx, refl _ ⟩,
    exact h hf,
  }, {
    intros y hy,
    cases hy with x hx,
    have u := h hx.1,
    rw ← hx.2,
    exact u,
  }
end

example (h : injective f) : f ⁻¹' (f '' A) ⊆ A := begin
  intros x xs,
  cases xs with y ys,
  rw ← (h ys.2),
  exact ys.1,
end

example : f '' (f⁻¹' C) ⊆ C := begin
  rw im_subset_iff_subset_inv,
end

example (h : surjective f) : C ⊆ f '' (f⁻¹' C) := begin
  intros x xs,
  cases h x with y ys,
  use y,
  split,
  rw ← ys at xs,
  exact xs,
  exact ys,
end

lemma im_of_subset (h : A ⊆ B) : f '' A ⊆ f '' B := begin
  intros x xs,
  cases xs with y ys,
  use y,
  split,
  exact h ys.1,
  exact ys.2,
end

example (h : C ⊆ D) : f ⁻¹' C ⊆ f ⁻¹' D := begin
  intros x xs,
  exact h xs,
end

example : f ⁻¹' (C ∪ D) = f ⁻¹' C ∪ f ⁻¹' D := 
begin
  trivial,
end

example : f '' (A ∩ B) ⊆ f '' A ∩ f '' B := 
begin
  intros x xs,
  cases xs with y ys,
  split; use y,
  exact ⟨ys.1.1,ys.2⟩,
  exact ⟨ys.1.2,ys.2⟩,
end

example (h : injective f) : f '' A ∩ f '' B ⊆ f '' (A ∩ B) := 
begin
  intros x xs,
  cases xs.1 with a ha,
  cases xs.2 with b hb,
  use b,
  have hfab : f a = f b, {
    rw ha.2,
    rw hb.2,
  },
  have hab : a = b := h hfab,
  rw hab at ha,
  split, {
    exact ⟨ ha.1, hb.1 ⟩,
  }, {
    exact hb.2,
  }
end

example : f '' A \ f '' B ⊆ f '' (A \ B) := begin
  intros x xs,
  cases xs.1 with a ha,
  use a,
  split, split, {
    exact ha.1,
  }, {
    intro hb,
    apply not_mem_of_mem_diff xs,
    use a,
    exact ⟨ hb, ha.2 ⟩,
  }, {
    exact ha.2,
  }
end

example : f ⁻¹' C \ f ⁻¹' D ⊆ f ⁻¹' (C \ D) := begin
  intros x xs,
  split, {
    have h := mem_of_mem_diff xs,
    exact h,
  }, {
    have h := not_mem_of_mem_diff xs,
    exact h,
  }
end

example : f '' A ∩ D = f '' (A ∩ f ⁻¹' D) := begin
  ext, split; intro h, {
    cases h.1 with a ha,
    use a,
    split, split, {
      exact ha.1,
    }, {
      change f a ∈ D,
      rw ha.2,
      exact h.2,
    }, {
      exact ha.2,
    }
  }, {
    cases h with a ha,
    split, {
      use a, split, {
        exact ha.1.1,
      }, {
        exact ha.2,
      }
    },
    rw ←ha.2,
    exact ha.1.2,
  }
end

example : f '' (A ∩ f ⁻¹' C) ⊆ f '' A ∪ C := 
begin
  have h1 : f '' A ≤ f '' A ∪ C := subset_union_left (f '' A) C,
  have h2 : f '' (A ∩ f ⁻¹' C) ≤ f '' A, {
    intros x xs,
    cases xs with a ha,
    use a,
    exact ⟨ ha.1.1, ha.2 ⟩, 
  },
  have h := le_trans h2 h1,
  exact h,
end

example : A ∩ f ⁻¹' C ⊆ f ⁻¹' (f '' A ∩ C) := begin
  intros x xs,
  split, {
    use x,
    exact ⟨ xs.1, refl _ ⟩,
  }, {
    exact xs.2,
  }
end

example : A ∪ f ⁻¹' C ⊆ f ⁻¹' (f '' A ∪ C) := begin
  intros x xs,
  cases xs with hx, {
    use x,
    exact ⟨ hx, refl _ ⟩,
  }, {
    right,
    exact xs,
  }
end

example : f '' (⋃ i, X i) = ⋃ i, f '' X i := 
begin
  ext, 
  rw mem_Union,
  split; intro h, {
    cases h with a ha,
    rw mem_Union at ha,
    cases ha.1 with i hi,
    use i,
    rw ←ha.2,
    use a,
    exact ⟨ hi, refl _ ⟩,
  }, {
    cases h with i hi,
    cases hi with a ha,
    use a, split, {
      rw mem_Union,
      use i, 
      exact ha.1,
    }, 
    exact ha.2,
  }
end

example : f '' (⋂ i, X i) ⊆ ⋂ i, f '' X i := begin
  intros x xs,
  rw mem_Inter,
  intro i,
  cases xs with a ha,
  rw mem_Inter at ha,
  use a,
  exact ⟨ ha.1 i, ha.2 ⟩,
end

example : f ⁻¹' (⋃ i, Y i) = ⋃ i, f ⁻¹' (Y i) := 
begin
  ext, split,
  all_goals {
    intro h,
    unfold preimage at *,
    dsimp at *,
    rw mem_Union at *,
    exact h,
  },
end

example : f ⁻¹' (⋂ i, Y i) = ⋂ i, f ⁻¹' (Y i) := begin
  ext, split,
  all_goals {
    intro h,
    unfold preimage at *,
    dsimp at *,
    rw mem_Inter at *,
    exact h,
  },
end

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := { x | x ∉ f x },
  cases surjf S with x xs,
  suffices h : x ∉ f x, {
    apply h,
    rw xs,
    exact h,
  },
  intro h,
  have h' : x ∉ f x, {
    rw xs at h,
    exact h,
  },
  exact h' h,
end

end function_variables
