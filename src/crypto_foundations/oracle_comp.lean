import crypto_foundations.comp

/-!
# Model of Nondeterministic Computation With Oracles

This file extends the `comp` monad to allow compuation with oracle access.
The definition allows for oracles to hide their internal state,
  which wouldn't be possible by just giving the adversary an explicit function.
It also allows for definitions that restrict the type of calls made to the oracle,
  e.g. an `oracle_comp M S (M × S)` attempting to forge a signature on an unqueried message.
-/

variables {A B C : Type}

/-- `oracle_comp A B C` is the type of a computation of a value of type `C`,
  with access to an oracle taking values in `A` to values in `B`.
  `oc_run` represents computing `oc` with `ob` as a proxy for the oracle
  -- Lack of impredicative `Set` type means this moves up a type universe
  TODO: the final return type can't be inferred in general without type hints -/
inductive oracle_comp : Type → Type → Type → Type 1
| oc_query {A B : Type} : Π (a : A), oracle_comp A B B
| oc_ret {A B C : Type} : Π (c : comp C), oracle_comp A B C
| oc_bind {A B C D : Type} : Π (oc : oracle_comp A B C) (od : C → oracle_comp A B D),
    oracle_comp A B D
| oc_run {A B C A' B' S : Type} [decidable_eq A] [decidable_eq B] [decidable_eq S] :
    Π (oc : oracle_comp A B C) (ob : S → A → oracle_comp A' B' (B × S)) (s : S), 
      oracle_comp A' B' (C × S)

namespace oracle_comp

/-- Every oracle_comp gives rise to a mapping from query assignments to the base comp type,
  where the value in `C` is the result of the computation if oracles behave like the input,
  and internal `comp` values return their base values
  -- TODO: rename this -/
def oracle_comp_base_exists (oc : oracle_comp A B C) : (A → B) → C :=
@oracle_comp.rec_on (λ A B C _, (A → B) → C) A B C oc
  (λ A B a q, q a) (λ A B C cc hcc, cc.comp_base_exists)
  (λ A B C D oc od hoc hod q, hod (hoc q) q)
  (λ A B C A' B' S hA hB hS oc ob s hoc hob q, ⟨hoc (λ a, (hob s a q).1), s⟩)

def decidable_eq_of_oracle_comp (oc : oracle_comp A B C) : 
  (A → B) → (A → decidable_eq B) → decidable_eq C :=
@oracle_comp.rec_on (λ A B C _, (A → B) → (A → decidable_eq B) → decidable_eq C) 
  A B C oc (λ A B a t h, h a) 
  (λ A B C cc tcc hcc, comp.decidable_eq_of_comp cc) 
  (λ A B C D oc od hoc hod t h, hod (oracle_comp_base_exists oc t) t h)
  (λ A B C A' B' S hA hB hS oc ob s hoc hob t h, @prod.decidable_eq C S 
    (hoc (λ a, (oracle_comp_base_exists (ob s a) t).1) 
      (λ a, @decidable_eq_of_prod_left B S ⟨s⟩ (hob s a t h))) hS)

/-- Evaluation distribution of an `oracle_comp A B C` as a `comp A`.
`S` is the type of the internal state of the `A` to `B` oracle, and `s` is the initial state.
`f` takes the current oracle state and an `A` value, and computes a `B` value and new oracle state. -/
def eval_distribution (oc : oracle_comp A B C) :
  Π (S : Type) [decidable_eq S] (f : S → A → comp (B × S)) (s : S), comp (C × S) :=
begin
  induction oc with A B a A B C c A B C D oc od hoc hod A B C A' B' S' hA hB hS' oc ob s' hoc hob,
  { exact λ S hS o s, o s a },
  { intros S hS o s,
    haveI : decidable_eq C := comp.decidable_eq_of_comp c,
    refine c.bind (λ c, comp.ret (c, s)) },
  { introsI S hS o s,
    exact (hoc S o s).bind (λ cs', hod cs'.fst S o cs'.snd) },
  { introsI S hS o' s,
    specialize hoc (S' × S) (λ ss a, (hob ss.fst a S o' ss.snd).bind 
      (λ x, comp.ret (x.1.1, (x.1.2, x.2)))) (s', s),
    haveI : decidable_eq (C × S' × S) := comp.decidable_eq_of_comp hoc,
    haveI : inhabited (S' × S) := ⟨(s', s)⟩,
    haveI : decidable_eq C := decidable_eq_of_prod_left C (S' × S),
    refine (hoc.bind $ λ x, comp.ret ((x.1, x.2.1), x.2.2)) }
end

/-- Evaluation distribution for a stateless oracle with `f` simulating the oracle. -/
def stateless_eval_distribution [decidable_eq B] [decidable_eq C]
  (oc : oracle_comp A B C) (f : A → comp B) : comp C :=
begin
  let f' : unit → A → comp (B × unit) :=
    λ _ a, comp.bind (f a) (λ b, comp.ret (b, ())),
  refine (oc.eval_distribution unit f' ()).bind (λ c, comp.ret c.1),
end

@[simp]
instance stateless_eval_distribution_well_formed [decidable_eq B] [decidable_eq C]
  (oc : oracle_comp A B C) (f : A → comp B) :
  (oc.stateless_eval_distribution f).is_well_formed :=
begin
  sorry,
end


end oracle_comp