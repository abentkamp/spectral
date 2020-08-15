import field_theory.algebraic_closure
import missing_mathlib.field_thoery.splitting_field

universes u v w
noncomputable theory
open_locale classical big_operators
open polynomial

variables (k : Type u) [field k]

namespace is_alg_closed

variables [is_alg_closed k]

lemma degree_eq_one_of_irreducible {p : polynomial k} (h_nz : p ≠ 0) (hp : irreducible p) : 
  p.degree = 1 :=
degree_eq_one_of_irreducible_of_splits h_nz hp (polynomial.splits' _)

end is_alg_closed