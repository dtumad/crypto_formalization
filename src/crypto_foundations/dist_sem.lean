import crypto_foundations.comp
import measure_theory.probability_mass_function
import data.real.nnreal

import algebra.big_operators.basic

open_locale big_operators nnreal

noncomputable theory

variables {A B : Type}

namespace comp

section eval_distribution

/-- Used to bootstrap `eval_distribution` and `eval_distribution_ne_zero_iff` -/
private def eval_distribution' (ca : comp A) : 
  well_formed_comp ca → Σ (da : pmf A), plift (∀ (a : A), (da a ≠ 0 ↔ a ∈ ca.support)) :=
begin
  refine ca.rec_on _ _ _ _,
  { exact λ _ _ a _, ⟨pmf.pure a, plift.up (by simp)⟩ },
  { refine λ A B ca cb db da h, _,
    rw well_formed_comp_bind_iff at h,
    refine ⟨(db h.1).1.bind_on_support (λ b hb, (da b (h.2 b ((plift.down (db h.1).2 b).mp hb))).1), 
      plift.up (λ a, _)⟩,
    rw [mem_support_bind_iff, pmf.bind_on_support_apply,
      tsum_ne_zero_iff (pmf.bind_on_support.summable (db _).1 _ _)],
    split; rintro ⟨b, hb⟩; refine ⟨b, _⟩,
    { simp only [not_or_distrib, ne.def, mul_eq_zero] at hb,
      simp only [dif_neg hb.left] at hb,
      rwa [← plift.down (db h.1).2, ← plift.down (da b (h.2 b ((plift.down (db h.1).2 b).mp hb.1) )).2] },
    { have : (db h.1).1 b ≠ 0 := (plift.down (db h.1).2 _).mpr hb.1,
      simp only [not_or_distrib, ne.def, mul_eq_zero, dif_neg this],
      have := hb.1,
      rwa [← plift.down (db h.1).2, ← plift.down (da b (h.2 b this)).2] at hb } },
  { introsI A _ _ _ _,
    refine ⟨pmf.const A, plift.up (λ a, by simpa using card_ne_zero_of_inhabited)⟩ },
  { introsI A p hp ca da h,
    rw well_formed_comp_repeat_iff at h,
    have : ∃ a (ha : p a), (da h.1).1 a ≠ 0,
    { refine h.2.rec (λ a ha, _),
      rw mem_support_repeat at ha,
      refine ⟨a, ha.2, (plift.down (da h.1).2 _).2 ha.1⟩ },
    refine ⟨(da h.1).1.filter p this, 
      plift.up (λ a, by rw [mem_support_repeat ca p a, pmf.filter_apply_ne_zero_iff, 
        ← (plift.down (da h.1).2 _), set.mem_inter_iff, pmf.mem_support_iff, set.mem_def])⟩ }
end

/-- The denotational semantics of a `comp A` is the distribution of resulting values.
  This distribution is given in the form of a `pmf` on the type `A` of the computation.
  Defined for any computation with nonempty support, but only meaningful if `ca` is well formed -/
def eval_distribution (ca : comp A) (hca : well_formed_comp ca) : pmf A :=
(eval_distribution' ca hca).fst

theorem eval_distribution_ne_zero_iff (ca : comp A) (hca : well_formed_comp ca) (a : A) :
  (eval_distribution ca hca a) ≠ 0 ↔ a ∈ ca.support :=
(plift.down (eval_distribution' ca hca).snd) a

lemma eval_distribution_support_eq_support (ca : comp A) (hca : well_formed_comp ca) :
  (eval_distribution ca hca).support = ca.support :=
set.ext (λ a, eval_distribution_ne_zero_iff ca hca a)

@[simp] lemma eval_distribution_ret [decidable_eq A] (a : A) (h : well_formed_comp (ret a)) :
  eval_distribution (ret a) h = pmf.pure a := 
rfl

/-- If `ca b` is not well formed for all `b ∉ ca.support`, then we can only use `bind'`-/
lemma eval_distribution_bind' (cb : comp B) (ca : B → comp A) 
  (h : well_formed_comp (bind cb ca)) 
  (hb : well_formed_comp cb) (ha : ∀ b ∈ cb.support, well_formed_comp (ca b)) :
  eval_distribution (bind cb ca) h = (eval_distribution cb hb).bind_on_support
    (λ b hb, (eval_distribution (ca b) 
      (ha b (by rwa eval_distribution_support_eq_support at hb)))) := rfl

/-- If we generalize `ha` over all `b` we can further reduce the `bind'` above to `bind`-/
lemma eval_distribution_bind (cb : comp B) (ca : B → comp A)
  (h : well_formed_comp (bind cb ca))
  (hb: well_formed_comp cb) (ha : ∀ b, well_formed_comp (ca b)) : 
  eval_distribution (bind cb ca) h = (eval_distribution cb hb).bind
    (λ b, eval_distribution (ca b) (ha b)) :=
trans (by reflexivity) (pmf.bind_on_support_eq_bind (eval_distribution cb hb) _)

@[simp] lemma eval_distribution_rnd {A : Type} [inhabited A] [fintype A] [decidable_eq A] 
  (h : well_formed_comp (rnd A)) : eval_distribution (rnd A) h = pmf.const A := 
rfl

end eval_distribution

/-- Probability of a `comp bool` returning true -/
def Pr (ca : comp bool) (h : well_formed_comp ca) : ℝ≥0 := 
ca.eval_distribution h bool.tt

end comp