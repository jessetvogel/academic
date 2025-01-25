-- # Imports
-- At the start of every Lean file are the `import` statements
import data.nat.basic
import number_theory.padics


-- # Commands

-- `#check`: shows the type of the given expression
#check 17
#check ℕ

-- `#print`: shows the definition of the given expression
#print nat.add_assoc
#check nat.add_assoc

-- `#reduce`: applies reduction rules to convert the given
--            expression to a reduced form
#check  (λ (n : ℕ), n + 1) 5
#reduce (λ (n : ℕ), n + 1) 5


-- # Definitions and theorems

-- `inductive`: allows to define an inductive type

inductive Weekday
| monday    : Weekday
| tuesday   : Weekday
| wednesday : Weekday
| thursday  : Weekday
| friday    : Weekday
| saturday  : Weekday
| sunday    : Weekday

#print Weekday
#check Weekday


-- `structure`: different notation to define an inductive type
--              with a single constructor

structure Monoid (M : Type) :=
(m : M → M → M)
(e : M)
(assoc : ∀ (a b c : M), m a (m b c) = m (m a b) c)
(mul_one : ∀ (a : M), m a e = a)
(one_mul : ∀ (a : M), m e a = a)

#check @Monoid.mk


-- `theorem` or `lemma` or `example`

theorem unique_one'
  {M : Type}
  {mon : Monoid M}
  (x : M)
  (h : ∀ (y : M), mon.m x y = y)
  : x = mon.e := eq.trans (eq.symm (mon.mul_one x)) (h mon.e)

theorem unique_one
  {M : Type}
  {mon : Monoid M}
  (x : M)
  (h : ∀ (y : M), mon.m x y = y)
  : x = mon.e :=
begin
  specialize h mon.e,
  rw mon.mul_one at h,
  exact h,
end

-- `example` can be used similarly as `theorem`, but
-- without providing a name

example
  {M : Type}
  (mon : Monoid M)
  : mon.m mon.e mon.e = mon.e :=
begin
  rw mon.mul_one,
end
