import comp
import to_mathlib

universes u v w

def function_cost_model := ∀ {A : Type u} {B : Type v}, (A → B) → ℕ → Prop
def comp_cost_model := ∀ {A : Type}, Comp A → ℕ → Prop
def oracle_comp_cost_model := ∀ {A B C : Type}, Comp.Oracle_Comp A B C → (ℕ → ℕ) → Prop

/-- Defines an extensible axiomatic cost model for Lean functions -/
constant has_cost : function_cost_model.{u v}

class classical_cost_model (cm : function_cost_model.{0 1}) :=
(has_cost_of_le {A : Type 0} {B : Type 1} {f : A → B} {n m : ℕ} (hnm : n ≤ m) :
  cm f n → cm f m)
(has_cost_ret {A : Type} [decidable_eq A] : cm (Comp.ret : A → Comp A) 0)

namespace has_cost

/-- Axioms for deriving costs of functions from related functions -/
axiom has_cost_of_le {A B : Type*} {f : A → B} {n m : ℕ} (hnm : n ≤ m) :
  has_cost f n → has_cost f m

axiom has_cost_compose' {A B C : Type*} {f : A → B} {g : A → B → C} {n1 n2 n3 : ℕ} :
    has_cost f n1 → has_cost g n2 → (∀ a, has_cost (g a) n3) → has_cost (λ a, g a (f a)) (n1 + n2 + n3)

axiom has_cost_uncurry {A B C : Type*} {f : A → B → C} {n1 n2 : ℕ} :
    has_cost f n1 → (∀ a, has_cost (f a) n2) → has_cost (function.uncurry f) (n1 + n2)

axiom has_cost_curry {A B C : Type*} {f : A → B → C} {n : ℕ} :
    has_cost (function.uncurry f) n → has_cost f n

axiom has_cost_curry' {A B C : Type*} {f : A → B → C} {n : ℕ} {a : A} :
    has_cost (function.uncurry f) n → has_cost (f a) n

/-- Costs of basic commonly used functions -/
axiom has_cost_const' {A B : Type*} (b : B) :
  has_cost (λ _, b : A → B) 0

axiom has_cost_id' {A : Type*} : 
  has_cost (id : A → A) 0

axiom has_cost_fst' {A B : Type*} :
    has_cost (prod.fst : A × B → A) 0

axiom has_cost_snd' {A B : Type*} :
    has_cost (prod.snd : A × B → B) 0

axiom has_cost_ret {A : Type*} [decidable_eq A] :
  has_cost (Comp.ret : A → Comp A) 0

variables {A B C : Type*}

@[simp] lemma has_cost_id {n : ℕ} : has_cost (id : A → A) n :=
has_cost_of_le (zero_le n) has_cost_id'

@[simp] lemma has_cost_const {b : B} {n : ℕ} : has_cost (λ _, b : A → B) n :=
has_cost_of_le (zero_le n) (has_cost_const' _)

@[simp] lemma has_cost_fst {n : ℕ} : has_cost (prod.fst : A × B → A) n :=
has_cost_of_le (zero_le n) (has_cost_fst')

@[simp] lemma has_cost_snd {n : ℕ} : has_cost (prod.snd : A × B → B) n :=
has_cost_of_le (zero_le n) (has_cost_snd')

lemma has_cost_comp {f : A → B} {g : B → C} {n m : ℕ} (hf : has_cost f n) (hg : has_cost g m) : 
  has_cost (g ∘ f) (n + m) :=
by simpa using has_cost_compose' hf (has_cost_const' _) (λ a, hg)

lemma has_cost_curry_apply {A B C : Type} {f : (A × B) → C} {n : ℕ} (hf : has_cost f n) :
  has_cost (function.curry f) n :=
has_cost_curry (by simpa using hf)

end has_cost


inductive comp_cost (fm : function_cost_model) : comp_cost_model
| cost_ret {A : Type} [decidable_eq A] {a : A} :
    comp_cost (Comp.ret a) 0
| cost_bind {A B : Type} {ca : Comp A} {cb : A → Comp B} {n1 n2 n3 : ℕ} :
    comp_cost ca n1 → fm cb n2 → (∀ a, comp_cost (cb a) n3) → comp_cost (Comp.bind ca cb) (n1 + n2 + n3)

#check comp_cost has_cost