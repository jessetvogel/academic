import tactic.basic

namespace category_theory

class category (C : Sort*) :=
  (hom     : Π (X Y : C), Sort*)
  (id      : Π (X : C), hom X X)
  (comp    : Π {X Y Z : C}, (hom Y Z) → (hom X Y) → (hom X Z))
  (comp_id : ∀ {X Y : C} (f : hom X Y), comp f (id X) = f . obviously)
  (id_comp : ∀ {X Y : C} (f : hom X Y), comp (id Y) f = f . obviously)
  (assoc   : ∀ {W X Y Z : C} (f : hom W X) (g : hom X Y) (h : hom Y Z), comp (comp h g) f = comp h (comp g f) . obviously)

notation `𝟙`     := category.id   -- type as `\b1`
infixr ` ∘ `:80  := category.comp -- type as `\circ`
infixr ` ⟶ `:80 := category.hom  -- type as `\h`

section categories

variables {C : Sort*} [category C]
variables {X Y Z : C}
variables {f : X ⟶ Y} {g : Y ⟶ Z}

-- # Exercise
-- Prove that, for any object `X : C`, the identity morphism is the only morphism
-- such that `g ∘ f = g` for all morphisms `g : Y ⟶ X`.
example (f : X ⟶ X) (hf : ∀ {Y : C} (g : X ⟶ Y), g ∘ f = g) : f = 𝟙 X :=
begin
  sorry,
end

-- Some basic definitions in category theory
class mono (f : X ⟶ Y) : Prop :=
  (cancel : ∀ {Z : C} {g h : Z ⟶ X} (w : f ∘ g = f ∘ h), g = h)

class epi (f : X ⟶ Y) : Prop :=
  (cancel : ∀ {Z : C} {g h : Y ⟶ Z} (w : g ∘ f = h ∘ f), g = h)

class iso (f : X ⟶ Y) : Prop :=
  (inv : ∃ (g : Y ⟶ X), g ∘ f = 𝟙 X ∧ f ∘ g = 𝟙 Y)

class initial (X : C) : Prop :=
  (map : ∀ (Y : C), ∃ (f : X ⟶ Y), ∀ (g : X ⟶ Y), f = g)

class terminal (Y : C) : Prop :=
  (map : ∀ (X : C), ∃ (f : X ⟶ Y), ∀ (g : X ⟶ Y), f = g)

lemma initial_map (X Y : C) [initial X] : ∃ (f : X ⟶ Y), ∀ (g : X ⟶ Y), f = g := initial.map Y
lemma terminal_map (Y X : C) [terminal Y] : ∃ (f : X ⟶ Y), ∀ (g : X ⟶ Y), f = g := terminal.map X

-- # Exercise
-- Prove that the identity morphism on `X` is mono.
theorem id_mono : mono (𝟙 X) :=
begin
  sorry,
end

-- # Exercise
-- Prove that the identity morphism on `X` is epi.
theorem id_epi : epi (𝟙 X) :=
begin
  sorry,
end

-- # Exercise
-- Prove that the composition of two monos is mono.
theorem comp_mono (hf : mono f) (hg : mono g) : mono (g ∘ f) :=
begin
  sorry,
end

-- # Exercise
-- Prove that the composition of two epis is epi.
theorem comp_epi (hf : epi f) (hg : epi g) : epi (g ∘ f) :=
begin
  sorry,
end

-- # Exercise
-- Prove that the composition of two isomorphisms is an isomorphism.
theorem comp_iso (hf : iso f) (hg : iso g) : iso (g ∘ f) :=
begin
  sorry,
end

-- # Exercise
-- Prove that initial objects are unique up to isomorphism.
theorem initial_unique (X Y : C) [hx : initial X] [hy : initial Y] : ∃ (f : X ⟶ Y), iso f :=
begin
  sorry,
end

-- # Exercise
-- Prove that terminal objects are unique up to isomorphism.
theorem terminal_unique (X Y : C) [hx : terminal X] [hy : terminal Y] : ∃ (f : X ⟶ Y), iso f :=
begin
  sorry,
end

end categories

section examples

class poset (α : Sort*) :=
  (R : α → α → Prop)
  (refl  : ∀ x, R x x)
  (asymm : ∀ {x y}, R x y → R y x → x = y)
  (trans : ∀ {x y z}, R y z → R x y → R x z)

infixr ` ≤ `:80  := poset.R

-- # Exercise
-- Show that the type `Prop` has the structure of a partially ordered set,
-- where the relation `R` is given by implication, that is, `R P Q := P → Q`
instance poset_Prop : poset Prop := {
  R := λ P Q, P → Q,
  refl := sorry,
  asymm := sorry,
  trans := sorry,
}

-- # Exercise
-- Show that every partially ordered set is naturally a category, where `hom x y`
-- is given by the proposition `x ≤ y`
instance category_of_poset (C : Sort*) [poset C] : category C := {
  hom := λ (x y : C), x ≤ y,
  id := sorry,
  comp := sorry,
  comp_id := sorry,
  id_comp := sorry,
  assoc := sorry,
}

-- # Exercise
-- Show that types with functions form a category
instance category_of_types : category Type := {
  hom := λ α β, α → β,
  id := sorry,
  comp := sorry,
  comp_id := sorry,
  id_comp := sorry,
  assoc := sorry,
}

end examples

section functors

class functor {C D : Sort*} [category C] [category D] (F : C → D) :=
  (map : Π {X Y : C} (f : X ⟶ Y), F X ⟶ F Y)
  (id : ∀ (X : C), map (𝟙 X) = 𝟙 (F X))
  (comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (g ∘ f) = map g ∘ map f)

variables {C D : Sort*} [category C] [category D]
variables {F : C → D} [functor F]

def functor_map (F : C → D) [functor F] {X Y : C} (f : X ⟶ Y) : F X ⟶ F Y := functor.map f

class full (F : C → D) [functor F] : Prop :=
  (intro : ∀ {X Y : C} (g : F X ⟶ F Y), ∃ (f : X ⟶ Y), functor.map f = g)

class faithful (F : C → D) [functor F] : Prop :=
  (cancel : ∀ {X Y : C} {f g : X ⟶ Y} (h : functor_map F f = functor_map F g), f = g)

-- # Exercise
-- Prove that a full and faithful functor reflects initial objects.
example (F : C → D) [functor F] [full F] [faithful F] {X : C} (hx : initial (F X)) : initial X :=
begin
  sorry,
end

-- # Exercise
-- Prove that a full and faithful functor reflects terminal objects.
example (F : C → D) [functor F] [full F] [faithful F] {X : C} (hx : terminal (F X)) : terminal X :=
begin
  sorry,
end

-- # Exercise
-- Prove that a faithful functor reflects monos.
example (F : C → D) [functor F] [faithful F] {X Y : C} {f : X ⟶ Y} [hf : mono (functor_map F f)] : mono f :=
begin
  sorry,
end

-- # Exercise
-- Prove that a faithful functor reflects epis.
example (F : C → D) [functor F] [faithful F] {X Y : C} {f : X ⟶ Y} [hf : epi (functor_map F f)] : epi f :=
begin
  sorry,
end

-- # Exercise
-- Prove that if `F` is full and faithful, and `F X` is isomorphic to `F Y`, then `X` is isomorphic to `Y`
example (F : C → D) [functor F] [full F] [faithful F] {X Y : C} {f : F X ⟶ F Y} (hf : iso f) : ∃ (g : X ⟶ Y), iso g :=
begin
  sorry,
end

structure category_bundled :=
  (C : Sort*) (str : category C)

instance category_of_categories : category category_bundled := {
  hom := sorry,
  id := sorry,
  comp := sorry,
  comp_id := sorry,
  id_comp := sorry,
  assoc := sorry,
}

end functors

section natural_transformations

variables {C D : Sort*} [category C] [category D]

@[ext]
structure natural_transformation (F G : C → D) [functor F] [functor G] :=
  (map     : Π (X : C), F X ⟶ G X)
  (natural : ∀ {X Y : C} (f : X ⟶ Y), map Y ∘ functor_map F f = functor_map G f ∘ map X)

structure functor_bundled (C D : Sort*) [category C] [category D] :=
  (F : C → D) (str : functor F)

instance category_of_functors : category (functor_bundled C D) := {
  hom := sorry,
  id := sorry,
  comp := sorry,
  comp_id := sorry,
  id_comp := sorry,
  assoc := sorry,
}

end natural_transformations

end category_theory
