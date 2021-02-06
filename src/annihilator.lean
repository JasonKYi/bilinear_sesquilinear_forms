import linear_algebra.projection
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

/-- The `dual_annihilator` of a submodule `W` is the set of linear maps `φ` such 
  that `φ w = 0` for all `w ∈ W`. -/
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

/-- The `dual_restrict` of a submodule `W` of `M` is the linear map from the 
  dual of `M` to the dual of `W` such that the domain of each linear map is 
  restricted to `W`. -/
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

namespace subspace

open submodule linear_map

variables {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] 

-- We work in vector spaces because `exists_is_compl` only hold for vector spaces
/-- Given a subspace `W` of `V` and an element of its dual `φ`, `dual_lift W φ` is 
  the natural extenstion of `φ` to an element of the dual of `V`. -/
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

@[simp] lemma dual_lift_add (φ ψ : module.dual K W) : 
  W.dual_lift (φ + ψ) = W.dual_lift φ + W.dual_lift ψ := 
begin
  -- `change` is significantly slower than `show`
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

/-- The quotient by the `dual_annihilator` of a subspace is isomorphic to the 
  dual of that subspace. -/
noncomputable def quot_annihilator_equiv (W : subspace K V) : 
  W.dual_annihilator.quotient ≃ₗ[K] module.dual K W := 
(quot_equiv_of_eq _ _ W.dual_restrict_ker_eq_dual_anihilator).symm.trans $
  W.dual_restrict.quot_ker_equiv_of_surjective dual_restrict_surjective

/-- The representation of the dual of a subspace `W` of `V` as a subspace of 
  the dual of `V`. -/
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

/-- The natural linear map from the dual of a subspace `W` to `W.dual`. -/
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

/-- The natural isomorphism forom the dual of a subspace `W` to `W.dual`. -/
noncomputable def dual_equiv_dual (W : subspace K V) : 
  module.dual K W ≃ₗ[K] W.dual := 
linear_equiv.of_bijective W.dual_to_subspace_dual 
  dual_to_subspace_ker_eq_bot dual_to_subspace_range_eq_top

/- Next step
  V* / U∘ ≅ U*
  → V* / U* ≅ U∘ 
  → V / U ≅ U∘ ≅ U⊥
-/

section

open_locale classical

open finite_dimensional

variables {V₁ : Type*} [add_comm_group V₁] [vector_space K V₁]
variables [finite_dimensional K V] [finite_dimensional K V₁]

/-- Given isomorphic subspaces `p q` of vector spaces `V` and `V₁` respectively, 
  `p.quotient` is isomorphic to `q.quotient`. -/
noncomputable def linear_equiv.quot_equiv_of_equiv
  {p : subspace K V} {q : subspace K V₁}
  (f₁ : p ≃ₗ[K] q) (f₂ : V ≃ₗ[K] V₁) : p.quotient ≃ₗ[K] q.quotient := 
linear_equiv.of_findim_eq _ _ 
begin
  rw [← @add_right_cancel_iff _ _ (findim K p), findim_quotient_add_findim, 
    linear_equiv.findim_eq f₁, findim_quotient_add_findim, linear_equiv.findim_eq f₂],
end

/-- Given the subspaces `p q`, if `p.quotient ≃ₗ[K] q`, then `q.quotient ≃ₗ[K] p` -/
noncomputable def linear_equiv.quot_equiv_of_quot_equiv
  {p q : subspace K V} (f : p.quotient ≃ₗ[K] q) : q.quotient ≃ₗ[K] p := 
linear_equiv.of_findim_eq _ _ 
begin
  rw [← @add_right_cancel_iff _ _ (findim K q), findim_quotient_add_findim, 
    ← linear_equiv.findim_eq f, add_comm, findim_quotient_add_findim]  
end

-- dependency
instance [H : finite_dimensional K V] : finite_dimensional K (module.dual K V) := 
begin
  refine @linear_equiv.finite_dimensional _ _ _ _ _ _ _ _ _ H,
  have hB := classical.some_spec (exists_is_basis_finite K V),
  haveI := classical.choice hB.2,
  exact is_basis.to_dual_equiv _ hB.1
end

/-- The quotient by the dual is isomorphic to its dual annihilator.  -/
noncomputable def quot_dual_equiv_annihilator (W : subspace K V) : 
  W.dual.quotient ≃ₗ[K] W.dual_annihilator := 
linear_equiv.quot_equiv_of_quot_equiv $ 
  linear_equiv.trans W.quot_annihilator_equiv W.dual_equiv_dual

/-- The quotient by a subspace is isomorphic to its dual annihilator. -/
noncomputable def quot_equiv_annihilator (W : subspace K V) : 
  W.quotient ≃ₗ[K] W.dual_annihilator := 
begin
  refine linear_equiv.trans _ W.quot_dual_equiv_annihilator,
  refine linear_equiv.quot_equiv_of_equiv _ _,
  { refine linear_equiv.trans _ W.dual_equiv_dual,
    have hB := classical.some_spec (exists_is_basis_finite K W),
    haveI := classical.choice hB.2,
    exact is_basis.to_dual_equiv _ hB.1 },
  { have hB := classical.some_spec (exists_is_basis_finite K V),
    haveI := classical.choice hB.2,
    exact is_basis.to_dual_equiv _ hB.1 },
end

end

end subspace