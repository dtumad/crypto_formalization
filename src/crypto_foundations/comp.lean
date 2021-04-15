import data.bitvec.basic
import to_mathlib

universes u v

/-- computational monad to extend the base language of Lean for cryptography purposes.
  `rnd n` represents a computation of purely random bits, 
  and `repeat` can repeat a random computation until some predicate holds -/
inductive comp : Π (A : Type), Type 1
| ret {A : Type} [hA : decidable_eq A] : Π (a : A), comp A
| bind {A B : Type} : Π (cb : comp B) (ca : B → comp A), comp A
| rnd (A : Type) [inhabited A] [fintype A] [decidable_eq A] : comp A -- TODO: allow any fintype here
| repeat {A : Type} : Π (p : A → Prop) [decidable_pred p] (ca : comp A) , comp A

namespace comp
open comp

variables {A B C : Type}

/-- Every computation gives rise to at least one element of the return type, 
  in particular this is the result if all `rnd` calls return strings of `1` bits. -/
def comp_base_exists (ca : comp A) : A :=
@comp.rec_on (λ A _, A) A ca
  (λ A hA a, a) (λ A B cb ca b fa, fa b)
  (λ A hA fA dA, @arbitrary A hA) (λ A p hp ca a, a)

/-- Because only `ret` and `rnd` terminate computation, and `ret` requires `decidable_eq A`,
  every computation must return a type with decidable equality.
  This needs to be definitional to make `support` fully computable -/
def decidable_eq_of_comp (ca : comp A) : decidable_eq A :=
@comp.rec_on (λ A _, decidable_eq A) A ca
  (λ A hA a, hA) (λ A B cb ca hcb hca, hca cb.comp_base_exists)
  (λ A hA fA dA, dA) (λ A p hp ca h, h)

/-- alias because this situation is very common due to use of `bUnion` in support -/
def decidable_eq_of_comp' (cb : comp B) (ca : B → comp A) : decidable_eq A :=
comp.decidable_eq_of_comp $ bind cb ca

section support

/-- The support of `comp A` is the elements of `A` with non-zero probability of being computed -/
def support (ca : comp A) : finset A :=
ca.rec (λ _ _ a, {a}) 
  (λ A B cb ca hcb hca, @finset.bUnion B A (decidable_eq_of_comp' cb ca) hcb hca)
  (λ A hA fA dA, @finset.univ A fA) (λ A p hp ca, @finset.filter _ p hp)

@[simp] lemma support_ret [decidable_eq A] (a : A) :
  (ret a).support = {a} := rfl

@[simp] lemma mem_support_ret_iff [decidable_eq A] (a a' : A) : 
  a ∈ (ret a').support ↔ a = a' := by simp

@[simp] lemma support_bind (cb : comp B) (ca : B → comp A) :
  (bind cb ca).support = @finset.bUnion B A (decidable_eq_of_comp' cb ca) 
    cb.support (λ b, (ca b).support) := rfl

@[simp] lemma mem_support_bind_iff (cb : comp B) (ca : B → comp A) (a : A) :
  a ∈ (comp.bind cb ca).support ↔ ∃ (b : B), b ∈ cb.support ∧ a ∈ (ca b).support := by simp

@[simp] lemma support_rnd [inhabited A] [fintype A] [decidable_eq A] : 
  (rnd A).support = finset.univ := rfl

@[simp] lemma mem_support_rnd [inhabited A] [fintype A] [decidable_eq A] (a : A) : 
  a ∈ (rnd A).support := by simp

@[simp] lemma support_repeat (ca : comp A) (p : A → Prop) [decidable_pred p] :
  (repeat p ca).support = ca.support.filter p := rfl

@[simp] lemma mem_support_repeat (ca : comp A) (p : A → Prop) [decidable_pred p] (a : A) :
  a ∈ (repeat p ca).support ↔ a ∈ ca.support ∧ p a := by simp

end support

section well_formed_comp 

/-- A computation is well formed if both of the following conditions hold:
  1 - All sub-computations are well-formed (Trivial for `ret` and `rnd`)
  2 - The computation has non-empty support (Trivial for all but `repeat`)
  Such a computation is gaurunteed to have a non-empty support -/
inductive well_formed_comp : ∀ {A : Type}, comp A → Prop
| well_formed_ret {A : Type} [hA : decidable_eq A] (a : A) :
    well_formed_comp (@ret A hA a)
| well_formed_bind {A B : Type} (cb : comp B) (ca : B → comp A) 
    (hcb : well_formed_comp cb) 
    (hca : ∀ b ∈ cb.support, well_formed_comp (ca b)) :
    well_formed_comp (bind cb ca)
| well_formed_rnd {A : Type} [inhabited A] [fintype A] [decidable_eq A] :
    well_formed_comp (rnd A)
| well_formed_repeat {A : Type} (p : A → Prop) [decidable_pred p] (ca : comp A)
    (hca : well_formed_comp ca) (hpca : (repeat p ca).support.nonempty) :
    well_formed_comp (repeat p ca)

open well_formed_comp

@[simp] lemma well_formed_comp_ret [decidable_eq A] (a : A) : 
  well_formed_comp (ret a) :=
well_formed_ret a

@[simp] lemma well_formed_comp_bind_iff (cb : comp B) (ca : B → comp A) :
  well_formed_comp (cb.bind ca) ↔ 
    well_formed_comp cb ∧ ∀ b ∈ cb.support, well_formed_comp (ca b) :=
begin
  refine ⟨λ w, _, λ h, well_formed_bind cb ca h.1 h.2⟩,
  cases w,
  split; assumption,
end

@[simp] lemma well_formed_comp_rnd [inhabited A] [fintype A] [decidable_eq A] : 
  well_formed_comp (rnd A) :=
well_formed_rnd

@[simp] lemma well_formed_comp_repeat_iff (p : A → Prop) [hp : decidable_pred p] (ca : comp A) :
  well_formed_comp (@repeat A p hp ca) ↔ well_formed_comp ca ∧ (repeat p ca).support.nonempty :=
begin
  refine ⟨λ w, _, λ h, well_formed_repeat p ca h.1 h.2⟩,
  tactic.unfreeze_local_instances,
  cases w,
  split; assumption,
end

theorem support_nonempty_of_well_formed_comp (ca : comp A)
  (hca : well_formed_comp ca) : ca.support.nonempty :=
begin
  induction hca with _ _ _ _ _ cb ca _ _ hcb_ih hca_ih A hA fA dA _ _ _ _ _ ha _,
  { simp },
  { obtain ⟨b, hb⟩ := hcb_ih,
    obtain ⟨a, ha⟩ := hca_ih b hb,
    exact ⟨a, (mem_support_bind_iff cb ca a).2 ⟨b, hb, ha⟩⟩ },
  { exact ⟨@arbitrary A hA, @mem_support_rnd A hA fA dA _⟩ },
  { exact ha },
end

end well_formed_comp

section oracle_comp

/-- `oracle_comp A B C` is the type of a computation of a value of type `C`,
  with access to an oracle taking values in `A` to values in `B`.
  `oc_run` represents computing `oc` with `ob` as a proxy for the oracle
  TODO: the final return type can't be inferred in general without type hints -/
inductive oracle_comp : Type → Type → Type → Type 1
| oc_query {A B : Type} : Π (a : A), oracle_comp A B B
| oc_ret {A B C : Type} : Π (c : comp C), oracle_comp A B C
| oc_bind {A B C D : Type} : Π (oc : oracle_comp A B C) (od : C → oracle_comp A B D),
    oracle_comp A B D
| oc_run {A B C A' B' S : Type} [decidable_eq A] [decidable_eq B] [decidable_eq S] :
    Π (oc : oracle_comp A B C) (ob : S → A → oracle_comp A' B' (B × S)) (s : S), 
      oracle_comp A' B' (C × S)

/-- Every oracle_comp gives rise to a mapping from query assignments to the base comp type,
  where the value in `C` is the result of the computation if oracles behave like the input -/
def oracle_comp_base_exists (oc : oracle_comp A B C) : (A → B) → C :=
@oracle_comp.rec_on (λ A B C _, (A → B) → C) A B C oc
  (λ A B a q, q a) (λ A B C cc hcc, cc.comp_base_exists)
  (λ A B C D oc od hoc hod q, hod (hoc q) q)
  (λ A B C A' B' S hA hB hS oc ob s hoc hob q, ⟨hoc (λ a, (hob s a q).1), s⟩)

def decidable_eq_of_oracle_comp (oc : oracle_comp A B C) : 
  (A → B) → (A → decidable_eq B) → decidable_eq C :=
@oracle_comp.rec_on (λ A B C _, (A → B) → (A → decidable_eq B) → decidable_eq C) 
  A B C oc (λ A B a t h, h a) 
  (λ A B C cc tcc hcc, decidable_eq_of_comp cc) 
  (λ A B C D oc od hoc hod t h, hod (oracle_comp_base_exists oc t) t h)
  (λ A B C A' B' S hA hB hS oc ob s hoc hob t h, @prod.decidable_eq C S 
    (hoc (λ a, (oracle_comp_base_exists (ob s a) t).1) 
      (λ a, @decidable_eq_of_prod_left B S ⟨s⟩ (hob s a t h))) hS)

end oracle_comp

end comp
