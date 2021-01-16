import linear_algebra.bilinear_form
import linear_algebra.dual
import linear_algebra.dimension
import linear_algebra.direct_sum_module
import algebra.invertible

open_locale classical

universes u v w

namespace bilin_form

variables {M : Type u} {R : Type v} [add_comm_group M] [ring R] [module R M]

/-- The perpendicular submodule of a submodule `N` is the set of elements all of 
  which are orthogonal to all elements of `N`. -/
def ortho (B : bilin_form R M) (N : submodule R M) : submodule R M := 
{ carrier := { m | ∀ n ∈ N, is_ortho B m n },
  zero_mem' := λ x _, ortho_zero x,
  add_mem' := λ x y hx hy n hn, 
    by rw [is_ortho, add_left, show B x n = 0, by exact hx n hn, 
        show B y n = 0, by exact hy n hn, zero_add],
  smul_mem' := λ c x hx n hn, 
    by rw [is_ortho, smul_left, show B x n = 0, by exact hx n hn, mul_zero] }

end bilin_form

/-- `std_basis` is the standard basis for vectors. -/
noncomputable def std_basis {R : Type v} [ring R] {n : Type w} 
  (i : n) : n → R := λ j, if j = i then 1 else 0

namespace std_basis 

variables {R : Type v} [ring R] {n : Type w} 

lemma eq_update (m : n) : std_basis m = function.update 0 m (1 : R) := 
by { ext, rw function.update_apply, refl }

lemma linear_map.eq_std_basis (m : n) : 
  (std_basis m : n → R) = linear_map.std_basis R (λ _, R) m 1 := 
by { rw linear_map.std_basis_apply, exact eq_update m }

@[simp] lemma neq_eq_zero {i j : n} (h : i ≠ j) : std_basis i j = (0 : R) := 
  if_neg h.symm

@[simp] lemma eq_eq_one {i j : n} (h : i = j) : std_basis i j = (1 : R) := 
  if_pos h.symm

lemma is_basis [fintype n] : @is_basis n R (n → R) std_basis _ _ _ := 
begin
  convert pi.is_basis_fun R n,
  ext1 m, exact linear_map.eq_std_basis m, 
end

lemma dot_product_eq_val (v : n → R) (i : n) [fintype n]:
  v i = matrix.dot_product v (std_basis i) := 
begin
  rw [matrix.dot_product, finset.sum_eq_single i, eq_eq_one rfl, mul_one],
  exact λ _ _ hb, by rw [neq_eq_zero hb.symm, mul_zero],
  exact λ hi, false.elim (hi $ finset.mem_univ _)
end

end std_basis

namespace bilin_form 

variables {M : Type u} {R : Type v} 

/-- A nondegenerate bilinear form is a bilinear form such that the only element 
  that is orthogonal to every other element is `0`. -/
def nondegenerate [add_comm_group M] [ring R] [module R M] (B : bilin_form R M) := 
  ∀ m : M, (∀ n : M, B m n = 0) → m = 0

variables {n : Type w} [fintype n]
variables [add_comm_group M] [comm_ring R] [module R M]

section matrix

lemma matrix.to_lin'_apply' (A : matrix n n R) (v w : n → R) : 
  (matrix.to_bilin' A) v w = matrix.dot_product v (A.mul_vec w) :=
begin
  simp_rw [matrix.to_bilin'_apply, matrix.dot_product, 
           matrix.mul_vec, matrix.dot_product],
  refine finset.sum_congr rfl (λ _ _, _),
  rw finset.mul_sum,
  refine finset.sum_congr rfl (λ _ _, _),
  rw ← mul_assoc,
end

lemma matrix.dot_product_eq_zero 
  (v : n → R) (h : ∀ w, matrix.dot_product v w = 0) : v = 0 := 
begin
  refine funext (λ x, _),
  rw [std_basis.dot_product_eq_val v x, h _], refl,
end

lemma matrix.dot_product_vec_mul_eq_mul_vec {R : Type u} [ring R] 
  (A : matrix n n R) (v w : n → R) : 
  matrix.dot_product (A.vec_mul v) w = matrix.dot_product v (A.mul_vec w) := 
begin
  simp_rw [matrix.dot_product, matrix.vec_mul, matrix.mul_vec, 
    matrix.dot_product, finset.mul_sum, finset.sum_mul, ← mul_assoc],
  rw [finset.sum_comm]
end

/-- Let `A` be a symmetric matrix. Then `A` has trivial kernel, that is it is 
  invertible if and only if the induced bilinear form of `A` is nondegenerate. -/
theorem matrix.invertible_iff_nondegenerate (A : matrix n n R) 
  (temp : sym_bilin_form.is_sym A.to_bilin') : 
  A.to_bilin'.nondegenerate ↔ A.to_lin'.ker = ⊥ := 
begin
  rw linear_map.ker_eq_bot',
  split; intro h,
  { refine λ m hm, h _ (λ x, _),
    rw [matrix.to_lin'_apply] at hm,
    rw [temp, matrix.to_lin'_apply', hm], 
    exact matrix.dot_product_zero _ },
  { intros m hm, apply h, 
    refine matrix.dot_product_eq_zero _ (λ w, _),
    have := hm w,
    rwa [temp, matrix.to_lin'_apply', matrix.dot_product_comm] at this }
end

-- TODO:
-- We would like a necessary and sufficent condition on which A.to_bilin' is 
-- symmetric so the condition is a prop on matrices not the induced bilinear 
-- product.

end matrix

/-- Let `B` be a symmetric, nondegenerate bilinear form on a nontrivial module 
  `M` over the ring `R` with invertible `2`. Then, there exists some `x : M` 
  such that `B x x ≠ 0`. -/
lemma exists_bilin_form_self_neq_zero {B : bilin_form R M} 
  (hB₁ : B.nondegenerate) (hB₂ : sym_bilin_form.is_sym B) 
  (hK : ∃ x : M, x ≠ 0) [htwo : invertible (2 : R)] : ∃ x, B x x ≠ 0 :=
begin
  by_contra, push_neg at h,
  have : ∀ u v : M, 2 * B u v = 0,
  { intros u v,
    rw [show 2 * B u v = B u u + B v u + B u v + B v v, 
          by rw [h u, h v, hB₂ v u]; ring, 
        show B u u + B v u + B u v + B v v = B (u + v) (u + v), 
          by simp [← add_assoc], h _] },
  have hcon : ∀ u v : M, B u v = 0,
  { intros u v,
    rw [show 0 = htwo.inv_of * (2 * B u v), by rw this; ring], simp [← mul_assoc] },
  exact let ⟨v, hv⟩ := hK in hv $ hB₁ v (hcon v),
end

/- Let V be a finite dimensional vector space over the field K with the 
  nondegenerate bilinear form B. Then for all m ∈ M, f_m : M → R : n ↦ B m n is 
  a linear functional in the dual space.

  Furthermore, the map, φ : M → M* : m ↦ f_m is an isomorphism.
-/

/-- Given a bilinear form `B`, `to_dual_aux` maps elements `m` of the module `M`
  to the functional `λ x, B m x` in the dual space. -/
def to_dual_aux (B : bilin_form R M) (m : M) : module.dual R M := 
{ to_fun := λ n, B m n,
  map_add' := add_right m,
  map_smul' := λ _ _, by simp only [algebra.id.smul_eq_mul, smul_right] }

@[simp] lemma to_dual_aux_def {B : bilin_form R M} {m n : M} : 
  B.to_dual_aux m n = B m n := rfl

/-- Given a bilinear form `B` on the modual `M`, `to_dual' B` is the linear map 
  from `M` to its dual such that `to_dual B m` is the functional `λ x, B m x`. -/
def to_dual' (B : bilin_form R M) : M →ₗ[R] module.dual R M := 
{ to_fun := λ m, to_dual_aux B m,
  map_add' := by { intros, ext, simp },
  map_smul' := by { intros, ext, simp } }

variables {V : Type u} {K : Type v} 
variables [field K] [add_comm_group V] [vector_space K V] 
 
lemma to_dual'_injective (B : bilin_form R M) (hB : B.nondegenerate) : 
  function.injective (to_dual' B) :=
B.to_dual'.to_add_monoid_hom.injective_iff.2 (λ a ha, hB _ (linear_map.congr_fun ha))

section finite_dimensional

instance [H : finite_dimensional K V] : finite_dimensional K (module.dual K V) := 
begin
  refine @linear_equiv.finite_dimensional _ _ _ _ _ _ _ _ _ H,
  have hB := classical.some_spec (finite_dimensional.exists_is_basis_finite K V),
  haveI := classical.choice hB.2,
  exact is_basis.to_dual_equiv _ hB.1
end

variable [finite_dimensional K V] 

-- In order to show that `to_dual` is a surjective map we used the fact that 
-- the dimensions of a vector space equal to the dimensions of its dual.
-- So rather than working with modules over rings, we work with vecotor spaces
lemma to_dual'_bijective (B : bilin_form K V) (hB : B.nondegenerate) : 
  function.bijective (to_dual' B) :=
begin
  refine ⟨B.to_dual'_injective hB, _⟩,
  change function.surjective B.to_dual',
  refine (linear_map.injective_iff_surjective_of_findim_eq_findim 
    (linear_equiv.findim_eq _)).1 (B.to_dual'_injective hB),
  have hB := classical.some_spec (finite_dimensional.exists_is_basis_finite K V),
  haveI := classical.choice hB.2,
  exact is_basis.to_dual_equiv _ hB.1
end

/-- To dual is the `linear_equiv` with the underlying linear map `to_dual'`. -/
noncomputable def to_dual (B : bilin_form K V) (hB : B.nondegenerate) : 
  V ≃ₗ[K] module.dual K V := 
{ map_smul' := B.to_dual'.map_smul',
  .. add_equiv.of_bijective B.to_dual'.to_add_monoid_hom (to_dual'_bijective B hB) }

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
lemma span_inf_ortho_eq_bot {B : bilin_form K V} (hB₁ : B.nondegenerate) 
  (hB₂ : sym_bilin_form.is_sym B) {x : V} (hx : B x x ≠ 0) : 
  submodule.span K ({x} : set V) ⊓ 
    B.ortho (submodule.span K ({x} : set V)) = ⊥ := 
begin
  rw ← finset.coe_singleton,
  refine eq_bot_iff.2 (λ y h, _),
  rcases mem_span_finset.1 h.1 with ⟨μ, rfl⟩,
  have := h.2 x _,
  { rw finset.sum_singleton at this ⊢,
    suffices hμzero : μ x = 0,
    { rw [hμzero, zero_smul, submodule.mem_bot] },
    change B (μ x • x) x = 0 at this, rw [smul_left] at this,
    exact or.elim (zero_eq_mul.mp this.symm) id (λ hfalse, false.elim $ hx hfalse) },
  { rw submodule.mem_span; exact λ _ hp, hp $ finset.mem_singleton_self _ }
end

-- ↓ This lemma only applies in field since we use the inverse
lemma span_sup_ortho_eq_top {B : bilin_form K V} (hB₁ : B.nondegenerate) 
  (hB₂ : sym_bilin_form.is_sym B) {x : V} (hx : B x x ≠ 0) : 
  submodule.span K ({x} : set V) ⊔ 
    B.ortho (submodule.span K ({x} : set V)) = ⊤ := 
begin
  refine eq_top_iff.2 (λ y _, _), rw submodule.mem_sup,
  refine ⟨(B x y * (B x x)⁻¹) • x, _, y - (B x y * (B x x)⁻¹) • x, _, _⟩,
  { exact submodule.mem_span_singleton.2 ⟨(B x y * (B x x)⁻¹), rfl⟩ },
  { intros z hz,
    rcases submodule.mem_span_singleton.1 hz with ⟨μ, rfl⟩,
    simp [is_ortho, mul_assoc, inv_mul_cancel hx, hB₂ x] },
  { simp },
end

end finite_dimensional

end bilin_form

-- I would like to show that W ⊕ W^⊥ = V