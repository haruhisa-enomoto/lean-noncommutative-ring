/-
Copyright (c) 2022 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Haruhisa Enomoto.
-/
import ring_theory.ideal.basic
import ring_theory.ideal.local_ring
import tactic.noncomm_ring

/-!
# Noncommutative Jacobson radical and local ring

Let `R` be a (possibly noncommutative) ring. The *Jacobson radical* of `R` is defined to be the intersection of all maximal *left* ideals of `R`, which coincides with that of all maximal *right* ideals, so it is a two-sided ideal.

`R` is called a *nc-local ring* if it has a unique maximal *left* ideal. This conditions is equivalent to that it has a unique maximal *right* ideal.
(Note that this is simply called a *local ring* in the setting of noncommutative ring, but we call it *nc-local* to avoid confusion.)

## Main definitions

* `nc_jacobson R : ideal R`: the Jacobson radical of a ring `R`, defined by the intersection of all maximal *left* ideals.

* `nc_local R : Prop`: the assertion that `R` has a unique maximal *left* ideal.

## Main statements

* `mem_nc_jacobson_tfae`: several equivalent conditions for an element in `R` to contained in `nc_jacobson R`.

* `nc_jacobson_symm`: `nc_jacobson R` coincides with the intersection of all maximal *right* ideals, namely, `nc_jacobson Rᵐᵒᵖ`.

* `nc_local_tfae`: several equivalent conditions for `R` to be an nc-local ring.

## Implementation notes

We have already the typeclass `ring_theory.ideal.local_ring.local_ring` for a nc-local (semi)ring.
We use a different definition for a ring for the convenience of the proof.
`local_iff_nc_local` shows that `nc_local R` if and only if `R` is an instance of `local_ring`.
-/


universe u

open mul_opposite

section monoid

/-! ### Some lemmas on inverses in monoids -/

variables {M : Type u} {a : M} {b : M} [monoid M]

lemma op_is_unit_of_is_unit : is_unit a → is_unit (op a) :=
λ ⟨⟨_, _, hab, hba⟩, rfl⟩, ⟨⟨_, _, by { rw [←op_mul, ←op_one, hba] },
  by { rw [←op_mul, ←op_one, hab] }⟩, rfl⟩

lemma unop_is_unit_of_is_unit {x : Mᵐᵒᵖ} : is_unit x → is_unit (unop x) :=
λ ⟨⟨_, _, hxa, hax⟩, rfl⟩, ⟨⟨_, _, by { rw [←unop_mul, ←unop_one, hax] },
  by { rw [←unop_mul, ←unop_one, hxa] }⟩, rfl⟩

lemma op_is_unit {a : M} : is_unit (op a) ↔ is_unit a :=
⟨λ h, (unop_op a) ▸ unop_is_unit_of_is_unit h, op_is_unit_of_is_unit⟩

lemma unop_is_unit {x : Mᵐᵒᵖ} : is_unit (unop x) ↔ is_unit x :=
⟨λ h, (op_unop x) ▸ op_is_unit_of_is_unit h, unop_is_unit_of_is_unit⟩

lemma is_unit_iff_has_two_sided_inv :
  is_unit a ↔ ∃ x : M, a * x = 1 ∧ x * a = 1 :=
⟨λ ⟨⟨a, x, hax, hxa⟩, rfl⟩, ⟨x, hax, hxa⟩,
  λ ⟨x, hax, hxa⟩, ⟨⟨a, x, hax, hxa⟩, rfl⟩⟩


/-- An element `a : M` of a monoid has a left inverse if there is some `x : M` satisfying `x * a = 1`. -/
def has_left_inv (a : M) : Prop := ∃ x : M, x * a = 1

/-- An element `a : M` of a monoid has a right inverse if there is some `x : M` satisfying `a * x = 1`. -/
def has_right_inv (a : M) : Prop := ∃ x : M, a * x = 1

/-- An element of a monoid is a unit if and only if it has both a left inverse and a right inverse. -/
theorem is_unit_iff_has_left_inv_right_inv :
  (is_unit a) ↔ (has_left_inv a) ∧ (has_right_inv a) :=
⟨λ h, ⟨h.exists_left_inv, h.exists_right_inv⟩,
  λ ⟨⟨x, hxa⟩, ⟨y, hay⟩⟩, ⟨⟨a, x,
  by { convert hay, rw [←mul_one x, ←hay, ←mul_assoc, hxa, one_mul] }, hxa⟩, rfl⟩⟩

/-- An element of a monoid is a unit if it has a left inverse which also has a left inverse. -/
theorem is_unit_of_has_left_inv_of_has_left_inv :
  (b * a = 1) → (has_left_inv b) → is_unit a :=
λ hba ⟨c, hcb⟩, ⟨⟨a, b,
  by { convert hcb, rw [←one_mul a, ←hcb, mul_assoc, hba, mul_one] }, hba⟩, rfl⟩

end monoid

section ring

/-! ### Some lemmas on inverses in rings -/
variables {R : Type u} {a : R} {b : R} [ring R]

lemma one_add_mul_has_left_inv_swap :
  (has_left_inv (1 + a * b)) → (has_left_inv (1 + b * a)) :=
begin
  rintro ⟨u, hu⟩,
  existsi 1 - b * u * a,
  calc (1 - b * u * a) * (1 + b * a)
        = 1 + b * a - b * (u * (1 + a * b)) * a : by noncomm_ring
    ... = 1 : by rw [hu ,mul_one, add_sub_cancel],
end

lemma one_add_mul_has_right_inv_swap :
  (has_right_inv (1 + a * b)) → (has_right_inv (1 + b * a)) :=
begin
  rintro ⟨u, hu⟩,
  existsi 1 - b * u * a,
  calc (1 + b * a) * (1 - b*u*a)
      = 1 + b * a - b * ((1 + a * b ) * u) * a : by noncomm_ring
  ... = 1 : by rw [hu ,mul_one, add_sub_cancel],
end

lemma one_add_mul_is_unit_swap :
  (is_unit (1 + a * b)) → (is_unit (1 + b * a)) :=
begin
  repeat {rw is_unit_iff_has_left_inv_right_inv},
  rintro ⟨h₁, h₂⟩,
  exact ⟨one_add_mul_has_left_inv_swap h₁, one_add_mul_has_right_inv_swap h₂⟩,
end

end ring

namespace ideal
section nc_jacobson_radical
variables {R : Type u} [ring R]

/-! ### Jacobson radical of a ring -/

/--
For a semiring `R`, the Jacobson radical of `R` is the intersection of
all maximal left ideals of of `R`.
-/
def nc_jacobson (R : Type u) [semiring R] : ideal R :=
Inf {J : ideal R | J.is_maximal }

lemma has_left_inv_iff_span_top {x : R} :
  (has_left_inv x) ↔ (span ({x} : set R)) = ⊤ :=
begin
  split,
  { rintro ⟨a, hax⟩,
    apply eq_top_of_unit_mem _ x a _ hax,
    apply submodule.mem_span_singleton_self },
  { intro h,
    have : (1 : R) ∈ span ({x} : set R),
      { rw h, exact submodule.mem_top },
    exact (mem_span_singleton').mp this },
end

lemma not_has_left_inv_iff_mem_maximal {x : R} :
  ¬has_left_inv x ↔ ∃ M : ideal R, M.is_maximal ∧ x ∈ M :=
begin
  rw has_left_inv_iff_span_top,
  split,
  { intro hx,
    obtain ⟨M, hMmax, hxM⟩ := exists_le_maximal _ hx,
    exact ⟨M, hMmax, by {apply hxM, apply submodule.mem_span_singleton_self}⟩ },
  { rintro ⟨M, hMmax, hxM⟩ hcontra,
    refine hMmax.ne_top _,
    rwa [eq_top_iff, ← hcontra, span_le,
      set.singleton_subset_iff] },
end

lemma one_add_has_left_inv_of_mem_jacobson {x : R} :
  (x ∈ nc_jacobson R) → has_left_inv (1 + x):=
begin
  contrapose,
  rw not_has_left_inv_iff_mem_maximal,
  rintro ⟨M, hMmax, hxxM⟩ hx,
  refine hMmax.ne_top _,
  rw eq_top_iff_one,
  have hxM : x ∈ M := by { rw [nc_jacobson, mem_Inf] at hx, apply hx hMmax },
  exact (add_mem_cancel_right hxM).mp hxxM,
end

lemma one_add_mul_self_mem_maximal_of_not_mem_maximal {x : R} {M : ideal R} :
M.is_maximal → x ∉ M → ∃ a : R, 1 + a * x ∈ M :=
begin
  rintro hMmax hxM,
  have : (1 : R) ∈ M ⊔ span {x},
  { rw is_maximal_iff at hMmax,
    apply hMmax.2 _ _ le_sup_left hxM,
    apply mem_sup_right,
    apply submodule.mem_span_singleton_self },
  rw submodule.mem_sup at this,
  obtain ⟨m, hmM, y, hy, hmy⟩ := this,
  rw mem_span_singleton' at hy,
  obtain ⟨a, rfl⟩ := hy,
  existsi -a,
  rwa [←hmy, neg_mul, add_neg_cancel_right],
end

/--
The following are equivalent for an element `x` in a ring `R`.

0. `x` is in the Jacobson radical of `R`, that is, contained in every mximal left ideals.
1. `1 + a * x` has a left inverse for any `a : R`.
2. `1 + a * x` is a unit for any `a : R`.
3. `1 + x * b` is a unit for any `b : R`.
4. `1 + a * x * b` is a unit for any `a b : R`.
-/
theorem mem_nc_jacobson_tfae {R : Type u} [ring R] (x : R) : tfae [
  x ∈ nc_jacobson R,
  ∀ a : R, has_left_inv (1 + a * x),
  ∀ a : R, is_unit (1 + a * x),
  ∀ b : R, is_unit (1 + x * b),
  ∀ (a b : R), is_unit (1 + a * x * b)] :=
begin
  tfae_have : 1 → 2,
  { exact λ hx a, one_add_has_left_inv_of_mem_jacobson $
    (nc_jacobson R).smul_mem' a hx },
  tfae_have : 2 → 3,
  { intros hx a,
    obtain ⟨c, hc⟩ := hx a,
    apply is_unit_of_has_left_inv_of_has_left_inv hc,
    suffices : c = 1 + ( -c * a * x),
    { rw this, apply hx },
    calc c = c * (1 + a * x) + ( -c * a * x) : by noncomm_ring
      ...  = 1 + ( -c * a * x) : by rw hc },
  tfae_have : 3 → 5,
  { intros hx _ _,
    apply one_add_mul_is_unit_swap,
    rw ←mul_assoc,
    apply hx },
  tfae_have : 5 → 1,
  { intro h,
    by_contra hx,
    rw [nc_jacobson, submodule.mem_Inf] at hx,
    simp only [not_forall] at hx,
    rcases hx with ⟨M, hMmax, hxM⟩,
    refine hMmax.ne_top _,
    obtain ⟨a, ha⟩ := one_add_mul_self_mem_maximal_of_not_mem_maximal hMmax hxM,
    apply eq_top_of_is_unit_mem _ ha,
    specialize h a 1,
    rwa [mul_assoc, mul_one] at h },
  tfae_have : 3 ↔ 4,
  { split; exact λ h b, one_add_mul_is_unit_swap (h b) },
  tfae_finish,
end

/--
The definition of the Jacobson radical of a ring is left-right symmetric, that is,
the intersection of all maximal left ideals coincides with that of all maximal right ideals.
We express this by using the opposite ring `Rᵐᵒᵖ`.
-/
theorem nc_jacobson_symm {x : R} :
  (x ∈ nc_jacobson R) ↔ (op x ∈ nc_jacobson Rᵐᵒᵖ) :=
begin
  split,
  { intro hx,
    rw (mem_nc_jacobson_tfae $ op x).out 0 3,
    intro a,
    rw [←unop_is_unit, unop_add, unop_one, unop_mul, unop_op],
    apply ((mem_nc_jacobson_tfae x).out 0 2).mp hx },
  { intro hx,
    rw (mem_nc_jacobson_tfae x).out 0 3,
    intro a,
    rw [←op_is_unit, op_add, op_one, op_mul],
    apply ((mem_nc_jacobson_tfae $ op x).out 0 2).mp hx },
end

end nc_jacobson_radical

section nc_local_ring
variables {R : Type u} [ring R]
/-! ### Noncommutative local ring -/

/-- A ring is a nc-local ring if it has a unique maximal left ideal. -/
def nc_local (R : Type u) [ring R] : Prop :=
  (∃! I : ideal R, I.is_maximal)

lemma nc_local_iff_jacobson_is_maximal :
  nc_local R ↔ (nc_jacobson R).is_maximal :=
begin
  split,
  { rintro ⟨M, hMmax, hMuniq⟩,
    convert hMmax,
    have : {J : ideal R | J.is_maximal} = {M},
    { rw set.eq_singleton_iff_unique_mem, exact ⟨hMmax, hMuniq⟩ },
    rw [nc_jacobson, this],
    exact Inf_singleton },
  { intro h,
    refine ⟨nc_jacobson R, h, _⟩,
    intros M hMmax,
    exact (eq_top_or_eq_of_coatom_le h.1 (Inf_le hMmax)).resolve_left hMmax.ne_top },
end

lemma is_jacobson_of_nc_local_of_is_maximal {J : ideal R} :
  nc_local R → J.is_maximal → J = nc_jacobson R :=
λ ⟨I, hIuniq⟩ hJmax, (hIuniq.2 _ $ (nc_local_iff_jacobson_is_maximal).mp
  ⟨I, hIuniq⟩).symm ▸ hIuniq.2 _ hJmax

lemma nontrivial_of_nc_local : nc_local R → nontrivial R :=
λ ⟨M, hM⟩, nontrivial_of_ne 0 1 $ λ h, (ne_top_iff_one M).mp hM.1.ne_top (h ▸ zero_mem M)

/-- In a local ring, an element with a left inverse is automatically a unit. -/
lemma is_unit_of_nc_local_of_has_left_inv :
  nc_local R → ∀ (a : R), has_left_inv a → is_unit a :=
begin
  rintro h a ⟨x, hxa⟩,
  apply is_unit_of_has_left_inv_of_has_left_inv hxa,
  by_contra hx,
  suffices : is_unit (0 : R),
  { haveI := nontrivial_of_nc_local h,
    exact not_is_unit_zero this },
  obtain ⟨M, hMmax, hxM⟩ := (not_has_left_inv_iff_mem_maximal).mp hx,
  replace hxM : x ∈ nc_jacobson R := 
    (is_jacobson_of_nc_local_of_is_maximal h hMmax) ▸ hxM,
  replace hxM := ((mem_nc_jacobson_tfae x).out 0 3).mp hxM,
  specialize hxM (-a),
  rwa [mul_neg, hxa, add_right_neg] at hxM,
end

lemma nonunits_add_iff_is_unit_or_is_unit_one_sub_self :
  (∀ {a b : R}, a ∈ nonunits R → b ∈ nonunits R → a + b ∈ nonunits R) ↔
  ∀ (a : R), is_unit a ∨ is_unit (1 - a) :=
begin
  split,
  { intros h a,
    by_contra hcont,
    rw not_or_distrib at hcont,
    specialize h hcont.1 hcont.2,
    rw add_sub_cancel'_right at h,
    exact one_not_mem_nonunits h },
  { intros h a b,
    suffices : is_unit (a + b) → ¬is_unit a → is_unit b,
    { exact λ h₁ h₂ h₃, h₂ $ (this h₃) h₁ },
    rintro ⟨u, hucoe⟩ ha, -- u = a + b
    rw ←units.is_unit_units_mul u⁻¹,
    have : ↑u⁻¹ * b = 1 - ↑u⁻¹ * a,
    { rw [eq_sub_iff_add_eq, add_comm, ← mul_add],
      exact units.inv_mul_of_eq hucoe },
    rw this,
    apply (h (↑u⁻¹ * a)).resolve_left,
    rwa units.is_unit_units_mul u⁻¹ },
end

/--
The following are equivalent for a non-zero ring `R`.
0. `R` is a nc-local ring, that is, it has a unique maximal left ideal.
1. The set of nonunits coincides with the Jacobson radical.
2. For any `a : R`, either `a` or `1 - a` is unit.
3. The set of nonunits are closed under additions.
-/
theorem nc_local_tfae (R : Type u) [ring R] [nontrivial R] : tfae [
    nc_local R,
    nonunits R = nc_jacobson R,
    ∀ a : R, is_unit a ∨ is_unit (1 - a),
    ∀ {a b : R}, a ∈ nonunits R → b ∈ nonunits R → a + b ∈ nonunits R] :=
begin
  tfae_have : 1 → 3,
  { intros h a,
    rw or_iff_not_imp_left,
    intro ha,
    replace ha : ¬has_left_inv a :=
      ha ∘(is_unit_of_nc_local_of_has_left_inv h a),
    rw not_has_left_inv_iff_mem_maximal at ha,
    obtain ⟨M, hMmax, haM⟩ := ha,
    replace haM : a ∈ nc_jacobson R := 
      (is_jacobson_of_nc_local_of_is_maximal h hMmax) ▸ haM,
    rw (mem_nc_jacobson_tfae a).out 0 2 at haM,
    specialize haM (-1),
    rwa [neg_mul, one_mul, ←sub_eq_add_neg] at haM },
  tfae_have : 3 → 2,
  { intro h,
    apply subset_antisymm, swap,
    { exact let ⟨_, hmax⟩ := exists_maximal R in
      subset_trans (Inf_le hmax) (coe_subset_nonunits hmax.ne_top) },
    intros x hx,
    change x ∈ nc_jacobson R,
    rw [mem_nonunits_iff, is_unit_iff_has_left_inv_right_inv,
      not_and_distrib] at hx,
    cases hx with hleft hright,
    { rw (mem_nc_jacobson_tfae x).out 0 2,
      intro a,
      specialize h (- a * x),
      rw [neg_mul, sub_neg_eq_add] at h,
      apply h.resolve_left,
      intro hax,
      apply hleft,
      obtain ⟨b, hbax⟩ := hax.exists_left_inv,
      existsi -b * a,
      rwa [mul_assoc, neg_mul, ←mul_neg] },
    { rw (mem_nc_jacobson_tfae x).out 0 3,
      intro b,
      specialize h (- x * b),
      rw [neg_mul, sub_neg_eq_add] at h,
      apply h.resolve_left _,
      intro hxb,
      apply hright,
      obtain ⟨c, hxbc⟩ := hxb.exists_right_inv,
      existsi -b * c,
      rwa [neg_mul, mul_neg, ←mul_assoc, ←neg_mul] } },
  tfae_have : 2 → 1,
  { intro h,
    existsi nc_jacobson R,
    dsimp only,
    split,
    { rw [is_maximal_def, is_coatom],
      split,
      { rw [ne_top_iff_one, ←set_like.mem_coe, ←h],
        exact one_not_mem_nonunits },
      intro I,
      contrapose,
      intro hI,
      refine not_lt_of_le _,
      rw [←set_like.coe_subset_coe, ←h],
      exact coe_subset_nonunits hI },
    { intros I hImax,
      apply le_antisymm,
      { rw [←set_like.coe_subset_coe, ←h],
        exact coe_subset_nonunits hImax.ne_top },
      { exact Inf_le hImax } } },
  tfae_have : 4 ↔ 3,
  { exact nonunits_add_iff_is_unit_or_is_unit_one_sub_self },
  tfae_finish,
end

/--
The definition of a local ring is left-right symmetric, that is,
a ring has a unique maximal left ideal if and only if it has a unique maximal right ideal.
We express this by using the opposite ring `Rᵐᵒᵖ`.
-/
theorem local_ring_symm [nontrivial R] : (nc_local R) ↔ (nc_local Rᵐᵒᵖ) :=
begin
  split,
  { intro h,
    rw (nc_local_tfae Rᵐᵒᵖ).out 0 2,
    rw (nc_local_tfae R).out 0 2 at h,
    intro a,
    rw [←@unop_is_unit _ _ a, ←@unop_is_unit _ _ (1 - a)],
    apply h },
  { intro h,
    rw (nc_local_tfae R).out 0 2,
    rw (nc_local_tfae Rᵐᵒᵖ).out 0 2 at h,
    intro a,
    rw [←@op_is_unit _ _ a, ←@op_is_unit _ _ (1 - a)],
    apply h },
end

theorem local_iff_nc_local : (local_ring R) ↔ (nc_local R) :=
begin
  split,
  { rintro ⟨_, hlocal⟩, resetI,
    rwa (nc_local_tfae R).out 0 3 },
  { intro h,
    haveI := nontrivial_of_nc_local h,
    have := ((nc_local_tfae R).out 0 3).mp h,
    exact local_ring.mk (λ _ _ ha hb, this ha hb) },
end

end nc_local_ring
end ideal

#lint