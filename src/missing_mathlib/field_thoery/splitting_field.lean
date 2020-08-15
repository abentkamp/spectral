import field_theory.splitting_field

noncomputable theory
open_locale classical big_operators

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}

namespace polynomial

variables [field α] [field β] [field γ]
open polynomial

section splits

variables (i : α →+* β)

lemma degree_eq_one_of_irreducible_of_splits {p : polynomial β} 
  (h_nz : p ≠ 0) (hp : irreducible p) (hp_splits: splits (ring_hom.id β) p): 
  p.degree = 1 :=
begin
  rcases hp_splits,
  { contradiction },
  { apply hp_splits hp, simp }
end

end splits

end polynomial