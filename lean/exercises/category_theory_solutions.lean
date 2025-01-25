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
  specialize hf (𝟙 X),
  rw category.id_comp at hf,
  exact hf,
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
  constructor,
  intros Z g h,
  rw [category.id_comp, category.id_comp],
  exact id,
end

-- # Exercise
-- Prove that the identity morphism on `X` is epi.
theorem id_epi : epi (𝟙 X) :=
begin
  constructor,
  intros Z g h,
  rw [category.comp_id, category.comp_id],
  exact id,
end

-- # Exercise
-- Prove that the composition of two monos is mono.
theorem comp_mono (hf : mono f) (hg : mono g) : mono (g ∘ f) :=
begin
  constructor,
  intros Z s t hgf,
  apply hf.cancel,
  apply hg.cancel,
  rw [category.assoc, category.assoc] at hgf,
  exact hgf,
end

-- # Exercise
-- Prove that the composition of two epis is epi.
theorem comp_epi (hf : epi f) (hg : epi g) : epi (g ∘ f) :=
begin
  constructor,
  intros Z s t hgf,
  apply hg.cancel,
  apply hf.cancel,
  rw [← category.assoc, ← category.assoc] at hgf,
  exact hgf,
end

-- # Exercise
-- Prove that the composition of two isomorphisms is an isomorphism.
theorem comp_iso (hf : iso f) (hg : iso g) : iso (g ∘ f) :=
begin
  cases hf.inv with k hk,
  cases hg.inv with l hl,
  use k ∘ l,
  split,
  rw [category.assoc, ← category.assoc f g l, hl.1, category.id_comp, hk.1],
  rw [category.assoc, ← category.assoc l k f, hk.2, category.id_comp, hl.2],
end

-- # Exercise
-- Prove that initial objects are unique up to isomorphism.
theorem initial_unique (X Y : C) [hx : initial X] [hy : initial Y] : ∃ (f : X ⟶ Y), iso f :=
begin
  cases initial_map X Y with f hf,
  cases initial_map Y X with g hg,
  cases initial_map X X with k hk,
  cases initial_map Y Y with l hl,
  use f,
  use g,
  split,
  rw [← hk (𝟙 X), ← hk (g ∘ f)],
  rw [← hl (𝟙 Y), ← hl (f ∘ g)],
end

-- # Exercise
-- Prove that terminal objects are unique up to isomorphism.
theorem terminal_unique (X Y : C) [hx : terminal X] [hy : terminal Y] : ∃ (f : X ⟶ Y), iso f :=
begin
  cases terminal_map X Y with f hf,
  cases terminal_map Y X with g hg,
  cases terminal_map X X with k hk,
  cases terminal_map Y Y with l hl,
  use g,
  use f,
  split,
  rw [← hk (𝟙 X), ← hk (f ∘ g)],
  rw [← hl (𝟙 Y), ← hl (g ∘ f)],
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
  refl := λ P p, p, --sorry,
  asymm := λ P Q pq qp, by ext; exact ⟨pq, qp⟩, -- sorry,
  trans := λ P Q R qr pq p, qr (pq p), -- sorry,
}

-- # Exercise
-- Show that every partially ordered set is naturally a category, where `hom x y`
-- is given by the proposition `x ≤ y`
instance category_of_poset (C : Sort*) [poset C] : category C := {
  hom := λ (x y : C), x ≤ y,
  id := poset.refl, -- sorry,
  comp := by apply poset.trans, -- sorry,
  comp_id := by obviously, -- sorry,
  id_comp := by obviously, -- sorry,
  assoc := by obviously, -- sorry,
}

-- # Exercise
-- Show that types with functions form a category
instance category_of_types : category (Sort*) := {
  hom := λ α β, α → β,
  id := λ α, id, -- sorry,
  comp := λ α β γ g f x, g (f x), -- sorry,
  comp_id := by obviously, -- sorry,
  id_comp := by obviously, -- sorry,
  assoc := by obviously, -- sorry,
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
  constructor,
  intro Y,
  cases @initial.map _ _ _ hx (F Y) with Ff hFf,
  cases @full.intro _ _ _ _ F _ _ _ _ Ff with f hf,
  use f,
  intro g,
  specialize hFf (functor.map g),
  apply @faithful.cancel _ _  _ _ F _ _ _ _ f g,
  unfold functor_map,
  rw [← hFf, hf],
end

-- # Exercise
-- Prove that a full and faithful functor reflects terminal objects.
example (F : C → D) [functor F] [full F] [faithful F] {X : C} (hx : terminal (F X)) : terminal X :=
begin
  constructor,
  intro Y,
  cases @terminal.map _ _ _ hx (F Y) with Ff hFf,
  cases @full.intro _ _ _ _ F _ _ _ _ Ff with f hf,
  use f,
  intro g,
  specialize hFf (functor.map g),
  apply @faithful.cancel _ _  _ _ F _ _ _ _ f g,
  unfold functor_map,
  rw [← hFf, hf],
end

-- # Exercise
-- Prove that a faithful functor reflects monos.
example (F : C → D) [functor F] [faithful F] {X Y : C} {f : X ⟶ Y} [hf : mono (functor_map F f)] : mono f :=
begin
  constructor,
  intros Z g h hfgh,
  apply @faithful.cancel _ _ _ _ F _ _ _ _ g h,
  apply hf.cancel,
  unfold functor_map,
  rw [← functor.comp, ← functor.comp, hfgh],
end

-- # Exercise
-- Prove that a faithful functor reflects epis.
example (F : C → D) [functor F] [faithful F] {X Y : C} {f : X ⟶ Y} [hf : epi (functor_map F f)] : epi f :=
begin
  constructor,
  intros Z g h hfgh,
  apply @faithful.cancel _ _ _ _ F _ _ _ _ g h,
  apply hf.cancel,
  unfold functor_map,
  rw [← functor.comp, ← functor.comp, hfgh],
end

-- # Exercise
-- Prove that if `F` is full and faithful, and `F X` is isomorphic to `F Y`, then `X` is isomorphic to `Y`
example (F : C → D) [functor F] [full F] [faithful F] {X Y : C} {f : F X ⟶ F Y} (hf : iso f) : ∃ (g : X ⟶ Y), iso g :=
begin
  cases hf.inv with g hg,
  cases @full.intro _ _ _ _ F _ _ _ _ f with k hk,
  cases @full.intro _ _ _ _ F _ _ _ _ g with l hl,
  use k,
  use l,
  split,
  apply @faithful.cancel _ _ _ _ F _ _ _ _ _ _,
  unfold functor_map,
  rw [functor.comp, hk, hl, hg.1, functor.id],
  apply @faithful.cancel _ _ _ _ F _ _ _ _ _ _,
  unfold functor_map,
  rw [functor.comp, hk, hl, hg.2, functor.id],
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
  hom := λ B₁ B₂, @natural_transformation _ _ _ _ B₁.F B₂.F B₁.str B₂.str,
  id := λ B, {
      map := λ X, category.id (B.F X),
      natural := by { obviously, rw [category.id_comp, category.comp_id], }
  },
  comp := by {
    intros B₁ B₂ B₃ μ₁ μ₂,
    apply natural_transformation.mk _ _,
    exact λ X, (@natural_transformation.map _ _ _ _ _ _ B₂.str B₃.str μ₁ X) ∘ (@natural_transformation.map _ _ _ _ _ _ B₁.str B₂.str μ₂ X),
    intros X Y f,
    let n₁ := @natural_transformation.natural _ _ _ _ _ _ B₂.str B₃.str μ₁,
    let n₂ := @natural_transformation.natural _ _ _ _ _ _ B₁.str B₂.str μ₂,
    rw [category.assoc, n₂, ← category.assoc, n₁, category.assoc],
  },
  comp_id := by { obviously, rw category.comp_id, },
  id_comp := by { obviously, rw category.id_comp, },
  assoc := by { obviously, rw category.assoc, }
}

end natural_transformations

end category_theory
