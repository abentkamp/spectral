import ring_theory.polynomial.basic
import ring_theory.principal_ideal_domain
import data.polynomial.field_division
import missing_mathlib.data.multiset
import missing_mathlib.data.polynomial
import missing_mathlib.data.list.basic
import missing_mathlib.algebra.group.units

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

universes u v w

namespace polynomial

open principal_ideal_ring

lemma ne_0_of_mem_factors {α : Type v} [field α] {p q : polynomial α} 
  (hp : p ≠ 0) (hq : q ∈ factors p) : q ≠ 0 :=
begin
  intro h_q_eq_0,
  rw h_q_eq_0 at hq,
  apply hp ((associated_zero_iff_eq_zero p).1 _),
  rw ←multiset.prod_eq_zero hq,
  apply (factors_spec p hp).2
end


lemma exists_noninjective_factor_of_eval₂_0 {α : Type v} {β : Type w} 
  [field α] [decidable_eq α] [decidable_eq β] [add_comm_group β] [vector_space α β]
  (f : β →ₗ[α] β) (v : β) (hv : v ≠ 0) 
  (p : polynomial α) (h_p_ne_0 : p ≠ 0) (h_eval_p : (polynomial.eval₂ (algebra_map _ _) f p) v = 0) : 
  ∃ q ∈ factors p, ¬ function.injective ((polynomial.eval₂ (algebra_map _ _) f q : β →ₗ[α] β) : β → β) :=
begin
  obtain ⟨c, hc⟩ := (factors_spec p h_p_ne_0).2,
  have am_comm : ∀ (a : α) (b : β →ₗ[α] β), (algebra_map _ _) a * b = b * (algebra_map _ _) a := algebra.commutes',
  rw mul_unit_eq_iff_mul_inv_eq at hc,
  rw [hc,
    @eval₂_mul_noncomm _ (β →ₗ[α] β) _ _ _ (algebra_map α _) f (factors p).prod 
      (@has_inv.inv (units (polynomial α)) _ c) (λ x y, ( algebra.commutes' x y).symm),
    polynomial.eq_C_of_degree_eq_zero (polynomial.degree_coe_units (c⁻¹)),
    polynomial.eval₂_C, ← multiset.coe_to_list (factors p), multiset.coe_prod,
    eval₂_prod_noncomm (algebra_map α _) (λ x y, (am_comm x y).symm)] at h_eval_p,
  have h_noninj : ¬ function.injective ⇑(list.prod 
    (list.map (λ p, polynomial.eval₂ (algebra_map _ _) f p) (multiset.to_list (factors p))) *
    (algebra_map _ _) (polynomial.coeff ↑c⁻¹ 0)),
  { rw [←linear_map.ker_eq_bot, linear_map.ker_eq_bot', classical.not_forall],
    use v, 
    exact not_imp.2 (and.intro h_eval_p hv) },
  show ∃ q ∈ factors p, ¬ function.injective ((polynomial.eval₂ (algebra_map _ _) f q).to_fun),
  { classical,
    by_contra h_contra,
    simp only [not_exists, not_not] at h_contra, 
    have h_factors_inj : ∀ g ∈ (factors p).to_list.map (λ q, (polynomial.eval₂ (algebra_map _ _) f q).to_fun),
        function.injective g,
    { intros g hg,
      rw list.mem_map at hg,
      rcases hg with ⟨q, hq₁, hq₂⟩,
      rw multiset.mem_to_list at hq₁,
      rw ←hq₂,
      exact h_contra q hq₁ },
    refine h_noninj (function.injective.comp _ _),
    { unfold_coes,
      dsimp only [list.prod, (*), mul_zero_class.mul, semiring.mul, ring.mul],
      rw list.foldl_map' linear_map.to_fun linear_map.comp function.comp _ _ (λ _ _, rfl),
      rw list.map_map,
      unfold function.comp,
      apply function.injective_foldl_comp (λ g, h_factors_inj g) function.injective_id },
    { rw [←linear_map.ker_eq_bot, module.endomorphism_algebra_map_apply, linear_map.ker_smul, linear_map.ker_id],
      apply polynomial.coeff_coe_units_zero_ne_zero }
  }
end

lemma linear_independent_iff_eval₂ {α : Type v} {β : Type w}
  [decidable_eq α] [comm_ring α] [decidable_eq β] [add_comm_group β] [module α β]
  (f : β →ₗ[α] β) (v : β) : 
  linear_independent α (λ n : ℕ, (f ^ n) v)
    ↔ ∀ (p : polynomial α), polynomial.eval₂ (algebra_map _ _) f p v = 0 → p = 0 :=
begin
  rw linear_independent_iff,
  simp only [finsupp.total_apply],
  simp only [finsupp_sum_eq_eval₂], 
  refl
end

end polynomial