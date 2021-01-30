import linear_algebra.dual

universes u v w

variables {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
variable {W : submodule R M}

/-- The first isomorphism theorem for surjective linear maps. -/
noncomputable def linear_map.quot_ker_equiv_of_surjective 
  {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] 
  [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂]
  (f : M →ₗ[R] M₂) (hf : function.surjective f) : f.ker.quotient ≃ₗ[R] M₂ := 
f.quot_ker_equiv_range.trans
  (linear_equiv.of_top f.range (linear_map.range_eq_top.2 hf))

namespace submodule

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

namespace of_compl

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

noncomputable def proj_left_aux (h : is_compl P Q) (m : M) : P :=
classical.some (exists_unique_add_of_is_compl h m)

noncomputable def proj_right_aux 
  {P Q : submodule R M} (h : is_compl P Q) (m : M) : Q :=
classical.some (classical.some_spec (exists_unique_add_of_is_compl h m))

theorem sum (h : is_compl P Q) (m : M) :
  (proj_left_aux h m : M) + proj_right_aux h m = m :=
(classical.some_spec (classical.some_spec (exists_unique_add_of_is_compl h m))).1

theorem unique_sum (h : is_compl P Q) (m : M) :
  ∀ (r : P) (s : Q), (r : M) + s = m → r = 
  proj_left_aux h m ∧ s = proj_right_aux h m :=
(classical.some_spec (classical.some_spec (exists_unique_add_of_is_compl h m))).2

lemma unique_sum_left (h : is_compl P Q) (m : M) (r : P) (s : Q) 
  (hrs : (r : M) + s = m) : r = proj_left_aux h m :=
(unique_sum h m r s hrs).1

lemma unique_sum_right (h : is_compl P Q) (m : M) (r : P) (s : Q) 
  (hrs : (r : M) + s = m) : s = proj_right_aux h m :=
(unique_sum h m r s hrs).2

noncomputable def proj_left (h : is_compl P Q) : M →ₗ[R] P :=
{ to_fun := proj_left_aux h,
  map_add' := λ x y, begin
    refine (unique_sum h (x + y) 
      (proj_left_aux h x + proj_left_aux h y)
      (proj_right_aux h x + proj_right_aux h y) _).1.symm,
    conv_rhs {rw [← sum h x, ← sum h y]},
    simp [add_add_add_comm],
  end,
  map_smul' := λ r m, begin
    refine (unique_sum h (r • m) (r • proj_left_aux h m) 
      (r • proj_right_aux h m) _).1.symm,
    conv_rhs {rw [← sum h m]},
    simp,
  end }

@[simp] lemma proj_left_apply (h : is_compl P Q) (m : M) :
  proj_left h m = proj_left_aux h m := rfl

@[simp] lemma proj_left_left_inverse (h : is_compl P Q) : 
  (proj_left h).comp P.subtype = linear_map.id :=
begin
  ext, erw [linear_map.id_coe, id.def, coe_eq_coe, linear_map.comp_apply, 
    subtype_apply, proj_left_apply, ← unique_sum_left h x.1 x 0 (add_zero _)],
end

noncomputable def proj_right (h : is_compl P Q) : M →ₗ[R] Q :=
{ to_fun := proj_right_aux h,
  map_add' := λ x y, begin
    refine (unique_sum h (x + y) 
      (proj_left_aux h x + proj_left_aux h y)
      (proj_right_aux h x + proj_right_aux h y) _).2.symm,
    conv_rhs {rw [← sum h x, ← sum h y]},
    simp [add_add_add_comm],
  end,
  map_smul' := λ r m, begin
    refine (unique_sum h (r • m) (r • proj_left_aux h m) 
      (r • proj_right_aux h m) _).2.symm,
    conv_rhs {rw [← sum h m]},
    simp,
  end }

@[simp] lemma proj_right_apply (h : is_compl P Q) (m : M) :
  proj_right h m = proj_right_aux h m := rfl

@[simp] lemma proj_right_left_inverse (h : is_compl P Q) : 
  (proj_right h).comp Q.subtype = linear_map.id :=
begin
  ext, erw [linear_map.id_coe, id.def, coe_eq_coe, linear_map.comp_apply, 
    subtype_apply, proj_right_apply, ← unique_sum_right h x.1 0 x (zero_add _)],
end

lemma proj_right_symm_eq_proj_left (h : is_compl P Q) : 
  (proj_right h.symm) = proj_left h := 
begin
  ext, have := sum h.symm x,
  rw add_comm at this,
  simp [unique_sum_left h x (proj_right h.symm x) (proj_left h.symm x) this],
end

lemma proj_left_symm_eq_proj_right (h : is_compl P Q) : 
  (proj_left h.symm) = proj_right h := 
begin
  ext, have := sum h.symm x,
  rw add_comm at this,
  simp [unique_sum_right h x (proj_right h.symm x) (proj_left h.symm x) this],
end

noncomputable def of_is_compl 
  (h : is_compl P Q) (φ : P →ₗ[R] M₁) (ψ : Q →ₗ[R] M₁) : M →ₗ[R] M₁ := 
 φ.comp (proj_left h) + ψ.comp (proj_right h)

@[simp] lemma of_is_compl_left_apply 
  {φ : P →ₗ[R] M₁} {ψ : Q →ₗ[R] M₁} (h : is_compl P Q) (p : P) : 
  of_is_compl h φ ψ p.1 = φ p :=
begin
  obtain ⟨h₁, h₂⟩ := unique_sum h p.1 p 0 (add_zero _),
  simp only [of_is_compl, proj_left_apply, 
    proj_right_apply, subtype.val_eq_coe, 
    linear_map.comp_apply, linear_map.add_apply],
  erw [← h₁, ← h₂, linear_map.map_zero, add_zero]
end  

@[simp] lemma of_right_apply {P Q : submodule R M} 
  {φ : P →ₗ[R] M₁} {ψ : Q →ₗ[R] M₁} (h : is_compl P Q) (q : Q) : 
  of_is_compl h φ ψ q.1 = ψ q :=
begin
  obtain ⟨h₁, h₂⟩ := unique_sum h q.1 0 q (zero_add _),
  simp only [of_is_compl, proj_left_apply, 
    proj_right_apply, subtype.val_eq_coe, 
    linear_map.comp_apply, linear_map.add_apply],
  erw [← h₁, ← h₂, linear_map.map_zero, zero_add]
end  

end of_compl

namespace submodule

open of_compl

variables {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] 

noncomputable def dual_lift {K : Type u} {V : Type v} [field K] 
  [add_comm_group V] [vector_space K V] 
  {W : subspace K V} (φ : module.dual K W) : module.dual K V := 
let h := classical.indefinite_description _ W.exists_is_compl in of_is_compl h.2 φ 0

lemma dual_restrict_surjective {W : subspace K V} : 
  function.surjective W.dual_restrict :=
begin
  intros φ,
  refine ⟨dual_lift φ, _⟩,
  ext, rw [dual_restrict_apply, dual_lift, of_is_compl_left_apply],
end

-- V* / U∘ ≅ U*
noncomputable def quot_annihilator_equiv (W : submodule K V) : 
  W.dual_annihilator.quotient ≃ₗ[K] module.dual K W := 
(quot_equiv_of_eq _ _ W.dual_restrict_ker_eq_dual_anihilator).symm.trans $
  W.dual_restrict.quot_ker_equiv_of_surjective dual_restrict_surjective

/- Next step
  V* / U∘ ≅ U*
  → V* / U* ≅ U∘ 
  → V / U ≅ U∘ ≅ U⊥
-/

end submodule