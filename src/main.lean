import linear_algebra.bilinear_form
import linear_algebra.dual
import linear_algebra.dimension

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

noncomputable def std_basis {R : Type v} [ring R] {n : Type w} [fintype n] 
  (i : n) : n → R := λ j, if j = i then 1 else 0

namespace std_basis 

variables {R : Type v} [ring R] {n : Type w} [fintype n] 

lemma eq_update (m : n) : std_basis m = function.update 0 m (1 : R) := 
by { ext, rw function.update_apply, refl }

lemma linear_map.eq_std_basis (m : n) : 
  (std_basis m : n → R) = linear_map.std_basis R (λ _, R) m 1 := 
by { rw linear_map.std_basis_apply, exact eq_update m }

@[simp] lemma neq_eq_zero {i j : n} (h : i ≠ j) : std_basis i j = (0 : R) := 
  if_neg h.symm

@[simp] lemma eq_eq_one {i j : n} (h : i = j) : std_basis i j = (1 : R) := 
  if_pos h.symm

lemma is_basis : @is_basis n R (n → R) std_basis _ _ _ := 
begin
  convert pi.is_basis_fun R n,
  ext1 m, exact linear_map.eq_std_basis m, 
end

lemma dot_product_eq_val (v : n → R) (i : n) :
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

variables {n : Type w} [fintype n] [decidable_eq n] 
variables [add_comm_group M] [comm_ring R] [module R M]

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

-- ↓ Lemma not true for nonsymmetric bilinear forms
lemma matrix.invertible_iff_nondegenerate (A : matrix n n R) 
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

-- We would like a necessary and sufficent condition on which A.to_bilin' is 
-- symmetric


-- Okay, we prove the following:
/- Let M be a finite dimensional module over the (commutative?) ring R with the 
  nondegenerate bilinear form B. Then for all m ∈ M, f_m : M → R : n ↦ B m n is 
  a linear functional in the dual space.

  Furthermore, the map, φ : M → M* : m ↦ f_m is an isomorphism.

  pf. Second part.
-/

def to_dual_aux (B : bilin_form R M) (m : M) : module.dual R M := 
{ to_fun := λ n, B m n,
  map_add' := add_right m,
  map_smul' := λ _ _, by simp only [algebra.id.smul_eq_mul, smul_right] }

@[simp] lemma to_dual_aux_def {B : bilin_form R M} {m n : M} : 
  B.to_dual_aux m n = B m n := rfl

def to_dual' (B : bilin_form R M) : M →ₗ[R] module.dual R M := 
{ to_fun := λ m, to_dual_aux B m,
  map_add' := by { intros, ext, simp },
  map_smul' := by { intros, ext, simp } }

variables {V : Type u} {K : Type v} 
variables [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V]
 
lemma to_dual'_injective (B : bilin_form R M) (hB : B.nondegenerate) : 
  function.injective (to_dual' B) :=
B.to_dual'.to_add_monoid_hom.injective_iff.2 (λ a ha, hB _ (linear_map.congr_fun ha))

instance [H : finite_dimensional K V] : finite_dimensional K (module.dual K V) := 
begin
  refine @linear_equiv.finite_dimensional _ _ _ _ _ _ _ _ _ H,
  have hB := classical.some_spec (finite_dimensional.exists_is_basis_finite K V),
  haveI := classical.choice hB.2,
  exact is_basis.to_dual_equiv _ hB.1
end

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

noncomputable def to_dual (B : bilin_form K V) (hB : B.nondegenerate) : 
  V ≃ₗ[K] module.dual K V := 
{ map_smul' := B.to_dual'.map_smul',
  .. add_equiv.of_bijective B.to_dual'.to_add_monoid_hom (to_dual'_bijective B hB) }

end bilin_form

-- I would like to show that W ⊕ W^⊥ = V