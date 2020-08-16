import ring_theory.algebra


universes u v w u₁ v₁

namespace algebra

variables {R : Type u} {S : Type v} {A : Type w}
variables [comm_ring R] [comm_ring S] [ring A] [algebra R A]

lemma mul_sub_algebra_map_commutes (x : A) (r : R) : 
  x * (x - algebra_map R A r) = (x - algebra_map R A r) * x :=
by rw [mul_sub, ←commutes, sub_mul]

lemma mul_sub_algebra_map_pow_commutes (x : A) (r : R) (n : ℕ) : 
  x * (x - algebra_map R A r) ^ n = (x - algebra_map R A r) ^ n * x :=
begin
  induction n with n ih,
  { simp },
  { rw [pow_succ, ←mul_assoc, mul_sub_algebra_map_commutes, 
      mul_assoc, ih, ←mul_assoc], }
end

end algebra

-- Put below endomorphism algebra
lemma module.endomorphism_algebra_map_apply (R : Type u) (M : Type v)
  [comm_ring R] [add_comm_group M] [module R M] (a : R) : 
  (algebra_map R (M →ₗ[R] M)) a = a • linear_map.id := rfl

lemma module.endomorphism_algebra_map_apply2 (R : Type u) (M : Type v)
  [comm_ring R] [add_comm_group M] [module R M] (a : R) (m : M) : 
  (algebra_map R (M →ₗ[R] M)) a m = a • m := rfl
