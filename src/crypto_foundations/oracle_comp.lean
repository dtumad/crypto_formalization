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
| oc_ret {A B C : Type} [decidable_eq C] : Π (c : comp C), oracle_comp A B C
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
  (λ A B a q, q a) (λ A B C hC cc hcc, @comp.comp_base_exists C hC cc)
  (λ A B C D oc od hoc hod q, hod (hoc q) q)
  (λ A B C A' B' S hA hB hS oc ob s hoc hob q, ⟨hoc (λ a, (hob s a q).1), s⟩)

def decidable_eq_of_oracle_comp (oc : oracle_comp A B C) : 
  (A → B) → (A → decidable_eq B) → decidable_eq C :=
@oracle_comp.rec_on (λ A B C _, (A → B) → (A → decidable_eq B) → decidable_eq C) 
  A B C oc (λ A B a t h, h a) 
  (λ A B C hC cc tcc hcc, hC) 
  (λ A B C D oc od hoc hod t h, hod (oracle_comp_base_exists oc t) t h)
  (λ A B C A' B' S hA hB hS oc ob s hoc hob t h, @prod.decidable_eq C S 
    (hoc (λ a, (oracle_comp_base_exists (ob s a) t).1) 
      (λ a, @decidable_eq_of_prod_left B S ⟨s⟩ (hob s a t h))) hS)

section is_well_formed

@[class]
inductive is_well_formed : ∀ {A B C : Type}, oracle_comp A B C → Prop
| well_formed_oc_query {A B : Type} (a : A) : 
    is_well_formed (oc_query a : oracle_comp A B B)
| well_formed_oc_ret {A B C : Type} [decidable_eq C] 
    (c : comp C) (hc : c.is_well_formed) :
    is_well_formed (oc_ret c : oracle_comp A B C)
| well_formed_oc_bind {A B C D : Type} (oc : oracle_comp A B C) (od : C → oracle_comp A B D)
    (hoc : is_well_formed oc) (hod : ∀ c, is_well_formed $ od c) :
    is_well_formed (oc_bind oc od)
| well_formed_oc_run {A B C A' B' S : Type} [decidable_eq A] [decidable_eq B] [decidable_eq S]
    (oc : oracle_comp A B C) (ob : S → A → oracle_comp A' B' (B × S)) (s : S)
    (hoc : is_well_formed oc) (hob : ∀ s a, is_well_formed $ ob s a) :
    is_well_formed (oc_run oc ob s)

@[simp]
lemma oc_query_is_well_formed {A B : Type} (a : A) :
  (oc_query a : oracle_comp A B B).is_well_formed :=
is_well_formed.well_formed_oc_query a

instance oc_query.is_well_formed {A B : Type} (a : A) :
  (oc_query a : oracle_comp A B B).is_well_formed :=
by simp

-- @[simp]
-- lemma oc_ret_is_well_formed_iff {A B C : Type} [decidable_eq C] (c : comp C) :
--   (oc_ret c : oracle_comp A B C).is_well_formed ↔ c.is_well_formed :=
-- begin
--   refine ⟨λ h, _, λ h, is_well_formed.well_formed_oc_ret c h⟩,
--   cases h,
--   exact h_hc,
-- end

instance oc_ret.is_well_formed {A B C : Type} [decidable_eq C] 
  (c : comp C) [h : c.is_well_formed] : 
  (oc_ret c : oracle_comp A B C).is_well_formed :=
is_well_formed.well_formed_oc_ret c h

@[simp]
lemma oc_bind_is_well_formed_iff {A B C D : Type} 
  (oc : oracle_comp A B C) (od : C → oracle_comp A B D) :
  (oc_bind oc od).is_well_formed ↔ 
    oc.is_well_formed ∧ ∀ c, (od c).is_well_formed :=
begin
  sorry,
end

end is_well_formed

/-- Evaluation distribution of an `oracle_comp A B C` as a `comp A`.
`S` is the type of the internal state of the `A` to `B` oracle, and `s` is the initial state.
`o` takes the current oracle state and an `A` value, and computes a `B` value and new oracle state. -/
def eval_distribution (oc : oracle_comp A B C) : 
    Π [hB : decidable_eq B] [hC : decidable_eq C]
    {S : Type} [hS : decidable_eq S] (s : S) 
    (o : S → A → @comp (B × S) (@prod.decidable_eq B S hB hS)),   
    @comp (C × S) (@prod.decidable_eq C S hC hS) :=
begin
  unfreezingI { induction oc with A B a A B C c A B C D oc od hoc hod A B C A' B' S' hA hB hS' oc ob s' hoc hob },
  -- induction oc with A B a A B C c A B C D oc od hoc hod A B C A' B' S' hA hB hS' oc ob s' hoc hob,
  { exact λ hB hC S hS s o, o s a },
  { exact λ S hS s o,
      c.bind (λ x, @comp.ret (C × S) (@prod.decidable_eq C S (comp.decidable_eq_of_comp c) hS) (x, s)) },
  { exact λ S hS s o, (@hoc S hS s o).bind (λ cs', @hod cs'.fst S hS cs'.snd o) },
  { introsI S hS s o',
    specialize hoc (s', s) (λ ss a, (hob ss.fst a ss.snd o').bind 
      (λ x, comp.ret (x.1.1, (x.1.2, x.2)))),
    haveI : decidable_eq (C × S' × S) := comp.decidable_eq_of_comp hoc,
    haveI : inhabited (S' × S) := ⟨(s', s)⟩,
    haveI : decidable_eq C := decidable_eq_of_prod_left C (S' × S),
    refine (hoc.bind $ λ x, comp.ret ((x.1, x.2.1), x.2.2)) }
end

@[simp]
lemma eval_distribution_oc_query {A B S : Type} [decidable_eq S]
  (a : A) (s : S) (o : S → A → comp (B × S)) :
  (oc_query a : oracle_comp A B B).eval_distribution s o = o s a := 
rfl

@[simp]
lemma eval_distribution_oc_ret {A B C S : Type} [hS : decidable_eq S]
  (c : comp C) (s : S) (o : S → A → comp (B × S)) :
  (oc_ret c : oracle_comp A B C).eval_distribution s o =
    c.bind (λ x, @comp.ret (C × S) (@prod.decidable_eq C S (comp.decidable_eq_of_comp c) hS) (x, s)) :=
rfl 

@[simp]
lemma eval_distribution_oc_bind {A B C D S : Type} [hS : decidable_eq S]
  (oc : oracle_comp A B C) (od : C → oracle_comp A B D)
  (s : S) (o : S → A → comp (B × S)) :
  (oc_bind oc od).eval_distribution s o = 
    (oc.eval_distribution s o).bind (λ cs', (od cs'.1).eval_distribution cs'.2 o) :=
rfl

@[simp]
instance eval_distribution_well_formed {S : Type} [decidable_eq S] 
  (oc : oracle_comp A B C) [hoc : oc.is_well_formed] :
  ∀ (s : S) (o : S → A → comp (B × S)) (ho : ∀ s a, (o s a).is_well_formed),
    (oc.eval_distribution s o).is_well_formed :=
begin
  unfreezingI { induction oc with A B a A B C c A B C D oc od hoc' hod A B C A' B' S' hA hB hS' oc ob s' hoc hob generalizing },
  {
    intros s o ho,
    simpa only using ho s a,
  },
  {
    intros s o ho,
    simp,
    exact (oc_ret_is_well_formed_iff c).1 hoc,
  },
  {
    intros s o ho,
    simp,
    rw oc_bind_is_well_formed_iff at hoc,
    haveI : oc.is_well_formed := hoc.1,
    refine ⟨hoc' s o ho, λ c s' h, _⟩,
    haveI : (od c).is_well_formed := hoc.2 c,
    exact hod c s' o ho,
  },
  {
    sorry,
  }
end

/-- Evaluation distribution for a stateless oracle with `f` simulating the oracle. -/
def stateless_eval_distribution [decidable_eq B] [decidable_eq C]
  (oc : oracle_comp A B C) (f : A → comp B) : comp C :=
begin
  let f' : unit → A → comp (B × unit) :=
    λ _ a, comp.bind (f a) (λ b, comp.ret (b, ())),
  refine (oc.eval_distribution () f').bind (λ c, comp.ret c.1),
end

@[simp]
instance stateless_eval_distribution_well_formed [decidable_eq B] [decidable_eq C]
  (oc : oracle_comp A B C) [hoc : oc.is_well_formed]
  (o : A → comp B) [ho : ∀ a, (o a).is_well_formed] :
  (oc.stateless_eval_distribution o).is_well_formed :=
by simp [stateless_eval_distribution]


end oracle_comp