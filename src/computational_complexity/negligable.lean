import computational_complexity.polynomial_asymptotics

/-!
# Negligable Growth

This file defines the notion of a negligable function `f : ℕ → ℝ`.
For convenience, the definition is given in terms of `is_O`,
  with various lemmas to translate back to the definition in terms of constants
-/

-- TODO: remove namespace and space them explicitly (e.g. negligable.add)

open asymptotics

def negligable (f : ℕ → ℝ) :=
∀ (c : ℤ), is_O f (λ n, (n : ℝ) ^ c) filter.at_top

namespace negligable

lemma negligable_of_is_O {f g : ℕ → ℝ} (hg : negligable g)
  (h : is_O f g filter.at_top) : negligable f :=
λ c, h.trans $ hg c

lemma add_negligable {f g : ℕ → ℝ} (hf : negligable f) (hg : negligable g) :
  negligable (f + g) :=
λ c, (hf c).add $ hg c

@[simp] lemma zero_negligable : negligable (λ n, 0) :=
λ c, is_O_zero _ _

lemma negligable_of_eventually_le {f g : ℕ → ℝ} (hg : negligable g)
  (h : ∀ᶠ n in filter.at_top, ∥f n∥ ≤ ∥g n∥) : negligable f :=
hg.negligable_of_is_O $ is_O_iff.2 ⟨1, by simpa using h⟩

lemma negligable_of_is_O_pow_neg {f : ℕ → ℝ} (C : ℤ)
  (hf : ∀ (c : ℤ) (hc : c < C), is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligable f :=
begin
  intro c,
  by_cases hc : c < C,
  { exact hf c hc },
  { exact (hf (C - 1) (by linarith)).trans 
      (fpow_is_O_fpow_of_le (le_trans (by linarith) (not_lt.1 hc))) }
end

lemma negligable_final_iff_const (f : ℕ → ℝ) (C : ℤ) :
  negligable f ↔ ∀ (c : ℤ) (hc : c < C), ∃ (N : ℕ), ∀ n ≥ N, ∥f n∥ ≤ (n : ℝ) ^ c :=
begin
  refine ⟨λ h c hc, _, λ h, _⟩,
  {
    specialize h (c - 1),
    rw is_O_iff at h,
    obtain ⟨k, hk⟩ := h,
    rw filter.eventually_at_top at hk,
    obtain ⟨N, hN⟩ := hk,
    by_cases hk0 : k ≤ 0,
    { refine ⟨N, λ n hn, _⟩,
      refine le_trans (hN n hn) _,
      refine le_trans (mul_nonpos_iff.2 (or.inr ⟨hk0, abs_nonneg _⟩) : _ ≤ 0) (_ : 0 ≤ _),
      refine fpow_nonneg (nat.cast_nonneg n) (c) },
    replace hk0 : 0 < k := by linarith,
    obtain ⟨M, hM'⟩ := exists_nat_gt k,
    have hM : k ≤ ↑M := le_of_lt hM',
    have hM0 : M ≠ 0 := nat.cast_ne_zero.1 (ne_of_lt (lt_trans hk0 hM')).symm,
    use max N M,
    intros n hn,
    rw ge_iff_le at hn,
    rw max_le_iff at hn,
    specialize hN n (hn.1),
    simp [real.norm_eq_abs] at hN ⊢,
    refine le_trans hN _,
    have hn0 : (↑n : ℝ) ≠ 0 := λ h, hM0 (le_antisymm ((nat.cast_eq_zero.1 h) ▸ hn.2) zero_le'),
    have hn0' : 0 < (↑n : ℝ) := lt_of_le_of_ne (nat.cast_nonneg n) hn0.symm,
    have : abs ((↑n : ℝ) ^ (c - 1)) = (↑n)⁻¹ * (↑n ^ c) :=
      trans (abs_of_nonneg (fpow_nonneg (le_of_lt hn0') (c - 1))) (by field_simp [fpow_sub_one hn0]),
    rw [this, ← mul_assoc],
    refine (mul_le_iff_le_one_left (fpow_pos_of_pos hn0' c)).2 _,
    calc k * (↑n)⁻¹ ≤ k * k⁻¹ : mul_le_mul le_rfl ((inv_le_inv hn0' hk0).mpr 
          (le_trans hM (nat.cast_le.2 hn.2))) (inv_nonneg.2 (nat.cast_nonneg n)) (le_of_lt hk0)
      ... = 1 : mul_inv_cancel (ne_of_lt hk0).symm,
  },
  {
    refine negligable_of_is_O_pow_neg C _,
    intros c hc,
    specialize h c hc,
    obtain ⟨N, hN⟩ := h,
    rw is_O_iff,
    use 1,
    rw filter.eventually_at_top,
    refine ⟨N, λ x hx, _⟩,
    specialize hN x hx,
    refine le_trans (hN) _,
    simp,
  },
end

lemma negligable_iff_polynomial (f : ℕ → ℝ) :
  negligable f ↔ ∀ (p : polynomial ℝ) (hp : p ≠ 0), is_O f (λ n, (p.eval ↑n)⁻¹) filter.at_top :=
begin
  refine ⟨λ h p hp, _, λ h, _⟩,
  {
    specialize h (- p.nat_degree),
    refine h.trans _,
    simp only [fpow_neg],
    have h1 : ∀ᶠ (n : ℕ) in filter.at_top, ∥(n : ℝ) ^ (p.nat_degree : ℤ)∥ ≠ 0,
    { rw filter.eventually_at_top,
      refine ⟨1, λ x hx, _⟩,
      rw [ne.def, real.norm_eq_abs, abs_eq_zero],
      refine fpow_ne_zero (p.nat_degree : ℤ) _,
      refine nat.cast_ne_zero.2 _,
      refine ne_of_gt (lt_of_lt_of_le zero_lt_one hx),
    },
    have h2 : ∀ᶠ (n : ℕ) in filter.at_top, ∥p.eval ↑n∥ ≠ 0,
    {
      have := polynomial.eventually_no_roots p hp,
      rw filter.eventually_at_top at this ⊢,
      obtain ⟨x, hx⟩ := this,
      obtain ⟨n, hn⟩ := exists_nat_ge x,
      refine ⟨n, λ m hm, _⟩,
      specialize hx (m : ℝ) (hn.trans (nat.cast_le.2 hm)),
      rw [real.norm_eq_abs, ne.def, abs_eq_zero],
      exact hx,
    },
    refine (inv_is_O_inv_iff _ _ h1 h2).2 _,
    have := polynomial.is_O_of_degree_le p (polynomial.X ^ p.nat_degree) (by simp),
    have := is_O.comp_tendsto this (begin
      rw filter.tendsto_at_top,
      intro x,
      obtain ⟨m, hm⟩ := exists_nat_ge x,
      rw filter.eventually_at_top,
      refine ⟨m, λ y hy, hm.trans _⟩,
      refine nat.cast_le.2 hy,
    end : filter.tendsto (λ (n : ℕ), (↑n : ℝ)) filter.at_top filter.at_top),
    refine this.trans _,
    simp,
    exact is_O_refl _ _,
  },
  {
    refine negligable_of_is_O_pow_neg 0 (λ c hc, _),    
    refine (h (polynomial.X ^ (c.nat_abs)) begin
      refine pow_ne_zero _ _,
      refine polynomial.X_ne_zero,
    end).trans _,
    convert is_O_refl _ _,
    ext x,
    have : (x : ℝ) ^ c.nat_abs = x ^ (-c),
    by simp only [←int.of_nat_nat_abs_of_nonpos (le_of_lt hc), gpow_coe_nat],
    simp [this],
  }
end

@[simp]
lemma const_mul_negligable_iff (f : ℕ → ℝ) {c : ℝ} (hc : c ≠ 0) :
  negligable (λ n, c * f n) ↔ negligable f :=
begin
  simp only [negligable],
  refine forall_congr (λ x, ⟨λ h, _, λ h, _⟩),
  {
    refine is_O.trans _ h,
    refine is_O_self_const_mul c hc f filter.at_top,
  },
  {
    refine is_O.trans _ h,
    refine is_O_const_mul_self c f filter.at_top,
  }
end

@[simp]
lemma x_mul_negligable_iff (f : ℕ → ℝ) :
  negligable (λ n, (n : ℝ) * f n) ↔ negligable f :=
begin
  refine ⟨λ h, _, λ h c, _⟩,
  { refine h.negligable_of_eventually_le _,
    rw filter.eventually_at_top,
    refine ⟨1, λ x hx, _⟩,
    simp only [normed_field.norm_mul, real.norm_coe_nat],
    by_cases hfx : f x = 0,
    { simp [hfx] },
    { exact (le_mul_iff_one_le_left (norm_pos_iff.2 hfx)).2 (nat.one_le_cast.2 hx) } },
  { specialize h (c - 1),
    refine (is_O.mul (is_O_refl (λ (n : ℕ), (n : ℝ)) filter.at_top) h).trans (is_O_of_le _ _),
    simp only [normed_field.norm_mul, real.norm_coe_nat, normed_field.norm_fpow],
    intro x,
    by_cases hx : (x : ℝ) = 0,
    { by_cases hc : c = 0,
      { simp [hx, hc, zero_le_one] },
      { simp [hx, zero_fpow c hc] } },
    { rw [mul_comm (x : ℝ), fpow_sub_one hx, mul_assoc, inv_mul_cancel hx, mul_one] } }
end

@[simp]
lemma pow_mul_negligable_iff (f : ℕ → ℝ) (c : ℕ) :
  negligable (λ n, (n : ℝ) ^ c * f n) ↔ negligable f :=
begin
  induction c with c hc,
  { simp only [one_mul, pow_zero] },
  { simp_rw [← hc, pow_succ, mul_assoc, x_mul_negligable_iff] }
end

theorem mul_polynomial_negligable_iff (f : ℕ → ℝ) (p : polynomial ℝ) (hp0 : p ≠ 0) :
  negligable (λ n, (p.eval n) * f n) ↔ negligable f :=
begin
  split,
  {
    intro h,
    by_cases hp : 1 ≤ p.degree,
    { refine negligable_of_eventually_le h _,
      suffices : ∀ᶠ (n : ℕ) in filter.at_top, 1 ≤ ∥polynomial.eval ↑n p∥,
      {
        refine filter.mem_sets_of_superset this _,
        intros x hx,
        simp at ⊢ hx,
        by_cases hfx : f x = 0,
        { simp [hfx] },
        { refine (le_mul_iff_one_le_left (norm_pos_iff.2 hfx)).2 hx }
      },
      suffices : ∀ᶠ (x : ℝ) in filter.at_top, 1 ≤ ∥polynomial.eval x p∥,
      {
        rw comap_thing,
        refine filter.eventually_comap' this,
      },
      exact poly_help hp 1,
    },
    {
      rw [not_le] at hp,
      replace hp : p.degree ≤ 0 := begin
        contrapose! hp,
        rwa nat.with_bot.one_le_iff_zero_lt,
      end,
      
      have := polynomial.eq_C_of_degree_le_zero hp,
      have hpc0 : p.coeff 0 ≠ 0 := begin
        refine λ h, hp0 (this.trans (by simp only [h, ring_hom.map_zero])),
      end,
      rw [this] at h,
      simp at h,
      rw const_mul_negligable_iff _ hpc0 at h,
      exact h,
    }
  },
  {
    intro h,
    refine polynomial.induction_on' p _ _,
    {
      intros p q hp hq,
      simp_rw [polynomial.eval_add, add_mul],
      refine add_negligable hp hq,
    },
    {
      intros n x,
      by_cases hx : x = 0,
      { simp only [hx, zero_negligable, zero_mul, polynomial.monomial_zero_right, polynomial.eval_zero] },
      { simpa only [mul_assoc x, const_mul_negligable_iff _ hx, 
          pow_mul_negligable_iff, polynomial.eval_monomial] },
    }
  }
end

-- theorem two_pow_negligable : negligable (λ n, 1 / 2 ^ n) :=
-- begin
--   refine (negligable_final_iff_const _ 0).2 _,
--   intros c hc,
--   simp,
--   sorry,
-- end

end negligable