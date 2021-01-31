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
variables {P Q : submodule R M}

lemma exists_unique_add_of_is_compl (hc : is_compl P Q) (x : M) : 
  ∃ (p : P) (q : Q), (p.1 + q.1 = x ∧ ∀ (r : P) (s : Q), 
    r.1 + s.1 = x → r = p ∧ s = q) :=
begin
  obtain ⟨p, q, h⟩ := 
    submodule.mem_sup'.1 ((eq_top_iff.2 hc.2).symm ▸ mem_top : x ∈ P ⊔ Q),
  refine ⟨p, q, h, λ r s hrs, _⟩, 
  erw [← h, ← @add_right_cancel_iff _ _ (-s : M) (r + s) (p + q), 
       add_assoc, add_neg_self, add_zero, 
       ← @add_left_cancel_iff _ _ (-p : M) r (p + q + -s),
       ← add_assoc, ← add_assoc, add_left_neg, zero_add, add_comm, 
       ← sub_eq_add_neg, ← sub_eq_add_neg] at hrs,
  split; rw [← sub_eq_zero],
  { suffices : r.1 - p.1 ∈ Q,
    { rw [← coe_eq_coe, coe_sub],
      exact (submodule.mem_bot _).1 (hc.1 ⟨P.sub_mem r.2 p.2, this⟩) },
    erw hrs, exact Q.sub_mem q.2 s.2 },
  { suffices : s.1 - q.1 ∈ P,
    { rw [← coe_eq_coe, coe_sub],
      exact (submodule.mem_bot _).1 (hc.1 ⟨this, Q.sub_mem s.2 q.2⟩) },
    erw [← neg_mem_iff, neg_sub, ← hrs],
    exact P.sub_mem r.2 p.2 }
end .

noncomputable def of_is_compl 
  (h : is_compl P Q) (φ : P →ₗ[R] M₁) (ψ : Q →ₗ[R] M₁) : M →ₗ[R] M₁ := 
 φ.comp (linear_proj_of_is_compl P Q h) + ψ.comp (linear_proj_of_is_compl Q P h.symm)

@[simp] lemma of_is_compl_left_apply 
  (h : is_compl P Q) {φ : P →ₗ[R] M₁} {ψ : Q →ₗ[R] M₁} (p : P) : 
  of_is_compl h φ ψ (p : M) = φ p :=
by erw [of_is_compl, linear_map.add_apply, linear_map.comp_apply, 
        linear_proj_of_is_compl_apply_left, linear_map.comp_apply, 
        linear_proj_of_is_compl_apply_right, linear_map.map_zero, add_zero]

@[simp] lemma of_is_compl_right_apply {P Q : submodule R M} 
  (h : is_compl P Q) {φ : P →ₗ[R] M₁} {ψ : Q →ₗ[R] M₁} (q : Q) : 
  of_is_compl h φ ψ (q : M) = ψ q :=
by erw [of_is_compl, linear_map.add_apply, linear_map.comp_apply, 
        linear_proj_of_is_compl_apply_right, linear_map.comp_apply,
        linear_proj_of_is_compl_apply_left, linear_map.map_zero, zero_add]

@[simp] lemma of_is_compl_zero (h : is_compl P Q) : 
  (of_is_compl h 0 0 : M →ₗ[R] M₁) = 0 :=
begin
  ext, obtain ⟨p, q, rfl, _⟩ := exists_unique_add_of_is_compl h x,
  erw [linear_map.map_add, of_is_compl_left_apply, add_zero, linear_map.zero_apply]
end

@[simp] lemma of_is_compl_add (h : is_compl P Q) 
  {φ₁ φ₂ : P →ₗ[R] M₁} {ψ₁ ψ₂ : Q →ₗ[R] M₁} : 
  h.of_is_compl (φ₁ + φ₂) (ψ₁ + ψ₂) = h.of_is_compl φ₁ ψ₁ + h.of_is_compl φ₂ ψ₂ :=
begin
  ext, obtain ⟨p, q, rfl, _⟩ := exists_unique_add_of_is_compl h x,
  simp only [of_is_compl_left_apply, of_is_compl_right_apply, 
    linear_map.add_apply, linear_map.map_add, subtype.val_eq_coe],
end

@[simp] lemma of_is_compl_smul (h : is_compl P Q) 
  {φ : P →ₗ[R] M₁} {ψ : Q →ₗ[R] M₁} (c : R) : 
  h.of_is_compl (c • φ) (c • ψ) = c • h.of_is_compl φ ψ :=
begin
  ext, obtain ⟨p, q, rfl, _⟩ := exists_unique_add_of_is_compl h x,
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

noncomputable def quot_dual_equiv_annihilator (W : subspace K V) : 
  W.dual.quotient ≃ₗ[K] W.dual_annihilator := sorry

/- Next step
  V* / U∘ ≅ U*
  → V* / U* ≅ U∘ 
  → V / U ≅ U∘ ≅ U⊥
-/

end subspace
