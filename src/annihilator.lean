import linear_algebra.dual

universes u v w

variables {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]

/-- The first isomorphism theorem for surjective linear maps. -/
noncomputable def linear_map.quot_ker_equiv_of_surjective 
  {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] 
  [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂]
  (f : M →ₗ[R] M₂) (hf : function.surjective f) : f.ker.quotient ≃ₗ[R] M₂ := 
f.quot_ker_equiv_range.trans
  (linear_equiv.of_top f.range (linear_map.range_eq_top.2 hf))

namespace submodule

variable {W : submodule R M}

def dual_annihilator {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M]
  [module R M] (W : submodule R M) : submodule R $ module.dual R M := 
{ carrier := { φ | ∀ w ∈ W, φ w = 0 },
  zero_mem' := by simp,
  add_mem' :=  by { intros φ ψ hφ hψ w hw,
    rw [linear_map.add_apply, hφ w hw, hψ w hw, add_zero] },
  smul_mem' := by { intros c φ hφ w hw,
    rw [linear_map.smul_apply, hφ w hw, smul_zero] } }

@[simp] lemma mem_dual_annihilator (φ : module.dual R M) : 
  φ ∈ W.dual_annihilator ↔ ∀ w ∈ W, φ w = 0 := iff.rfl

def dual_restrict (W : submodule R M) : 
  module.dual R M →ₗ[R] module.dual R W := 
{ to_fun := λ φ, φ.dom_restrict W,
  map_add' := by simp [linear_map.ext_iff],
  map_smul' := by simp [linear_map.ext_iff] }.

@[simp] lemma dual_restrict_apply 
  (W : submodule R M) (φ : module.dual R M) (x : W) : 
  W.dual_restrict φ x = φ x.1 := rfl

lemma dual_restrict_ker_eq_dual_anihilator 
  (W : submodule R M) : W.dual_restrict.ker = W.dual_annihilator :=
begin
  ext φ, split; intro hφ,
  { intros w hw,
    rw linear_map.mem_ker at hφ,
    rw [← W.dual_restrict_apply φ ⟨w, hw⟩, hφ], refl },
  { ext, exact hφ x.1 x.2 }
end

end submodule

namespace is_compl

open submodule

open_locale classical

variables {M₁ : Type w} [add_comm_group M₁] [module R M₁]
variables {p q : submodule R M}

lemma exists_unique_add_of_is_compl (hc : is_compl p q) (x : M) : 
  ∃ (u : p) (v : q), (u.1 + v.1 = x ∧ ∀ (r : p) (s : q), 
    r.1 + s.1 = x → r = u ∧ s = v) :=
begin
  obtain ⟨u, v, h⟩ := 
    submodule.mem_sup'.1 ((eq_top_iff.2 hc.2).symm ▸ mem_top : x ∈ p ⊔ q),
  refine ⟨u, v, h, λ r s hrs, _⟩, 
  erw [← h, ← @add_right_cancel_iff _ _ (-s : M) (r + s) (u + v), 
       add_assoc, add_neg_self, add_zero, 
       ← @add_left_cancel_iff _ _ (-u : M) r (u + v + -s),
       ← add_assoc, ← add_assoc, add_left_neg, zero_add, add_comm, 
       ← sub_eq_add_neg, ← sub_eq_add_neg] at hrs,
  split; rw [← sub_eq_zero],
  { suffices : r.1 - u.1 ∈ q,
    { rw [← coe_eq_coe, coe_sub],
      exact (submodule.mem_bot _).1 (hc.1 ⟨p.sub_mem r.2 u.2, this⟩) },
    erw hrs, exact q.sub_mem v.2 s.2 },
  { suffices : s.1 - v.1 ∈ p,
    { rw [← coe_eq_coe, coe_sub],
      exact (submodule.mem_bot _).1 (hc.1 ⟨this, q.sub_mem s.2 v.2⟩) },
    erw [← neg_mem_iff, neg_sub, ← hrs],
    exact p.sub_mem r.2 u.2 }
end .

/-- Given linear maps `φ` and `ψ` from complement submodules, `of_is_compl` is 
the induced linear map over the entire module. -/
noncomputable def of_is_compl 
  (h : is_compl p q) (φ : p →ₗ[R] M₁) (ψ : q →ₗ[R] M₁) : M →ₗ[R] M₁ := 
 φ.comp (linear_proj_of_is_compl p q h) + ψ.comp (linear_proj_of_is_compl q p h.symm)

@[simp] lemma of_is_compl_left_apply 
  (h : is_compl p q) {φ : p →ₗ[R] M₁} {ψ : q →ₗ[R] M₁} (u : p) : 
  of_is_compl h φ ψ (u : M) = φ u :=
by erw [of_is_compl, linear_map.add_apply, linear_map.comp_apply, 
        linear_proj_of_is_compl_apply_left, linear_map.comp_apply, 
        linear_proj_of_is_compl_apply_right, linear_map.map_zero, add_zero]

@[simp] lemma of_is_compl_right_apply  
  (h : is_compl p q) {φ : p →ₗ[R] M₁} {ψ : q →ₗ[R] M₁} (v : q) : 
  of_is_compl h φ ψ (v : M) = ψ v :=
by erw [of_is_compl, linear_map.add_apply, linear_map.comp_apply, 
        linear_proj_of_is_compl_apply_right, linear_map.comp_apply,
        linear_proj_of_is_compl_apply_left, linear_map.map_zero, zero_add]

@[simp] lemma of_is_compl_zero (h : is_compl p q) : 
  (of_is_compl h 0 0 : M →ₗ[R] M₁) = 0 :=
begin
  ext, obtain ⟨_, _, rfl, _⟩ := exists_unique_add_of_is_compl h x,
  erw [linear_map.map_add, of_is_compl_left_apply, add_zero, linear_map.zero_apply]
end

@[simp] lemma of_is_compl_add (h : is_compl p q) 
  {φ₁ φ₂ : p →ₗ[R] M₁} {ψ₁ ψ₂ : q →ₗ[R] M₁} : 
  h.of_is_compl (φ₁ + φ₂) (ψ₁ + ψ₂) = h.of_is_compl φ₁ ψ₁ + h.of_is_compl φ₂ ψ₂ :=
begin
  ext, obtain ⟨_, _, rfl, _⟩ := exists_unique_add_of_is_compl h x,
  simp only [of_is_compl_left_apply, of_is_compl_right_apply, 
    linear_map.add_apply, linear_map.map_add, subtype.val_eq_coe],
end

instance : has_scalar R (M →ₗ[R] M₁) := linear_map.has_scalar

@[simp] lemma of_is_compl_smul (h : is_compl p q) 
  {φ : p →ₗ[R] M₁} {ψ : q →ₗ[R] M₁} (c : R) : 
  h.of_is_compl (c • φ) (c • ψ) = c • h.of_is_compl φ ψ :=
begin
  ext, obtain ⟨_, _, rfl, _⟩ := exists_unique_add_of_is_compl h x,
  simp only [of_is_compl_left_apply, of_is_compl_right_apply, linear_map.smul_apply, 
    eq_self_iff_true, linear_map.map_add, subtype.val_eq_coe],
end

end is_compl

namespace subspace

open is_compl submodule

variables {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] 

-- We work in vector spaces because `exists_is_compl` only hold for vector spaces
noncomputable def dual_lift 
  (W : subspace K V) (φ : module.dual K W) : module.dual K V := 
let h := classical.indefinite_description _ W.exists_is_compl in of_is_compl h.2 φ 0

variable {W : subspace K V}

@[simp] lemma dual_lift_of_subtype {φ : module.dual K W} (w : W) : 
  W.dual_lift φ (w : V) = φ w := 
by erw of_is_compl_left_apply _ w

lemma dual_lift_of_mem {φ : module.dual K W} {w : V} (hw : w ∈ W) : 
  W.dual_lift φ w = φ ⟨w, hw⟩ := 
dual_lift_of_subtype ⟨w, hw⟩

@[simp] lemma dual_lift_zero : W.dual_lift 0 = 0 := by simp [dual_lift]

-- `change` is significantly slower than `show`
@[simp] lemma dual_lift_add (φ ψ : module.dual K W) : 
  W.dual_lift (φ + ψ) = W.dual_lift φ + W.dual_lift ψ := 
begin
  show of_is_compl _ _ 0 = of_is_compl _ φ 0 + of_is_compl _ ψ 0,
  rw [← zero_add (0 : _ →ₗ[K] _), of_is_compl_add], simp
end

@[simp] lemma dual_lift_smul (c : K) (φ : module.dual K W) : 
  W.dual_lift (c • φ) = c • W.dual_lift φ := 
begin
  show of_is_compl _ _ 0 = c • of_is_compl _ _ 0,
  rw [← smul_zero c, of_is_compl_smul], simp
end 

lemma dual_restrict_surjective : 
  function.surjective W.dual_restrict :=
begin
  intros φ, refine ⟨W.dual_lift φ, _⟩, ext, 
  erw [dual_restrict_apply, dual_lift, of_is_compl_left_apply],
end

lemma dual_lift_injective : function.injective W.dual_lift :=
begin
  rintro _ _ h, 
  ext, rw [← dual_lift_of_subtype, h, dual_lift_of_subtype], 
end

-- V* / U∘ ≅ U*
noncomputable def quot_annihilator_equiv (W : subspace K V) : 
  W.dual_annihilator.quotient ≃ₗ[K] module.dual K W := 
(quot_equiv_of_eq _ _ W.dual_restrict_ker_eq_dual_anihilator).symm.trans $
  W.dual_restrict.quot_ker_equiv_of_surjective dual_restrict_surjective

def dual (W : subspace K V) : subspace K (module.dual K V) := 
{ carrier := { φ | ∃ ψ : module.dual K W, φ = W.dual_lift ψ },
  zero_mem' := ⟨0, dual_lift_zero.symm⟩,
  add_mem' := 
    by { rintro _ _ ⟨ψ₁, rfl⟩ ⟨ψ₂, rfl⟩, 
         exact ⟨ψ₁ + ψ₂, (dual_lift_add ψ₁ ψ₂).symm⟩ },
  smul_mem' := 
    by { rintro c _ ⟨ψ, rfl⟩,
         exact ⟨c • ψ, (dual_lift_smul c ψ).symm⟩ } }

@[simp] lemma mem_dual_iff (φ : module.dual K V) : φ ∈ W.dual ↔ 
  ∃ ψ : module.dual K W, φ = W.dual_lift ψ := iff.rfl

noncomputable def dual_to_subspace_dual (W : subspace K V) : 
  module.dual K W →ₗ[K] W.dual := 
{ to_fun := λ φ, ⟨W.dual_lift φ, ⟨φ, rfl⟩⟩,
  map_add' := by { intros _ _, simp_rw [dual_lift_add], refl },
  map_smul' := by { intros _ _, simp_rw [dual_lift_smul], refl } }

@[simp] lemma dual_to_subspace_dual_apply (φ : module.dual K W) : 
  W.dual_to_subspace_dual φ = ⟨W.dual_lift φ, ⟨φ, rfl⟩⟩ := rfl

lemma dual_to_subspace_ker_eq_bot : 
  W.dual_to_subspace_dual.ker = ⊥ :=
linear_map.ker_eq_bot.2 $ λ φ ψ h, dual_lift_injective (subtype.mk_eq_mk.1 h)

lemma dual_to_subspace_range_eq_top : 
  W.dual_to_subspace_dual.range = ⊤ := 
linear_map.range_eq_top.2 $ λ ⟨φ, hφ⟩, let ⟨ψ, hψ⟩ := hφ in
  ⟨ψ, by rw [dual_to_subspace_dual_apply, subtype.mk_eq_mk, hψ]⟩

noncomputable def dual_equiv_subspace_dual (W : subspace K V) : 
  module.dual K W ≃ₗ[K] W.dual := 
linear_equiv.of_bijective W.dual_to_subspace_dual 
  dual_to_subspace_ker_eq_bot dual_to_subspace_range_eq_top

-- example (U : subspace K V) : W.quotient ≃ₗ[K] U := by suggest

noncomputable def quot_dual_equiv_annihilator (W : subspace K V) : 
  W.dual.quotient ≃ₗ[K] W.dual_annihilator := sorry

/- Next step
  V* / U∘ ≅ U*
  → V* / U* ≅ U∘ 
  → V / U ≅ U∘ ≅ U⊥
-/

end subspace

-- def foo' (p q : submodule R M) (f : p ≃ₗ[R] q): p.quotient ≃ₗ[R] q.quotient := 
-- begin
--   sorry
-- end

-- def foo (P Q : submodule R M) (f : P.quotient ≃ₗ[R] Q) : Q.quotient ≃ₗ[R] P := 
-- begin
  
  
  
-- end

/-
def restrict_to_dual (B : bilin_form R₃ M₃) (W : submodule R₃ M₃) :
  W →ₗ[R₃] module.dual R₃ M₃ := (to_dual' B).comp (linear_map.inclusion W)

@[simp] lemma restrict_to_dual_def {B : bilin_form R₃ M₃} {W : submodule R₃ M₃}
  {w : M₃} (hw : w ∈ W) : B.restrict_to_dual W ⟨w, hw⟩ = B.to_dual' w := rfl

lemma restrict_to_dual_ker_eq {B : bilin_form R₃ M₃} {W : submodule R₃ M₃}
  (hB : B.nondegenerate) : (B.restrict_to_dual W).ker = ⊥ :=
begin
  rw eq_bot_iff,
  rintro ⟨x, hx⟩ hker,
  convert (⊥ : submodule R₃ W).zero_mem,
  refine hB _ _, intro n,
  change B.to_dual' x = 0 at hker,
  rw [← to_dual'_def, hker], refl,
end

lemma restrict_to_dual_range {B : bilin_form R₃ M₃} {W : submodule R₃ M₃}
  (hB : B.nondegenerate) {w w' : M₃} (hw : w ∈ W) (hw' : w' ∈ B.orthogonal W) :
  B.restrict_to_dual W ⟨w, hw⟩ w' = 0 :=
begin
  simp, --exact hw' w hw, Does orthogonality commute?
  sorry
end

-/