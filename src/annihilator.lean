import linear_algebra.dual

universes u v w

/-- The first isomorphism theorem for surjective linear maps. -/
noncomputable def linear_map.quot_ker_equiv_of_surjective 
  {R : Type u} {M : Type v} {M₂ : Type w} [comm_ring R] 
  [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂]
  (f : M →ₗ[R] M₂) (hf : function.surjective f) : f.ker.quotient ≃ₗ[R] M₂ := 
f.quot_ker_equiv_range.trans
  (linear_equiv.of_top f.range (linear_map.range_eq_top.2 hf))

example {R : Type u} {M : Type v} [comm_ring R] 
  [add_comm_group M] [module R M] : 
  (⊤ : submodule R M) ≃ₗ[R] M := linear_equiv.of_top ⊤ rfl

namespace submodule

def dual_annihilator {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M]
  [module R M] (W : submodule R M) : submodule R $ module.dual R M := 
{ carrier := { φ | ∀ w ∈ W, φ w = 0 },
  zero_mem' := by simp,
  add_mem' :=  by { intros φ ψ hφ hψ w hw,
    rw [linear_map.add_apply, hφ w hw, hψ w hw, add_zero] },
  smul_mem' := by { intros c φ hφ w hw,
    rw [linear_map.smul_apply, hφ w hw, smul_zero] } }

variables {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
variable {W : submodule R M}

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

section of_compl

open_locale classical

variables {M₁ : Type w} [add_comm_group M₁] [module R M₁]

lemma exists_unique_add_of_is_compl {P Q : submodule R M} 
  (hc : is_compl P Q) (x : M) : ∃ (p : P) (q : Q), 
  (p.1 + q.1 = x ∧ ∀ (r : P) (s : Q), r.1 + s.1 = x → r = p ∧ s = q) :=
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

noncomputable def of_is_compl {P Q : submodule R M} 
  (h : is_compl P Q) (φ : P →ₗ[R] M₁) (ψ : Q →ₗ[R] M₁) : M →ₗ[R] M₁ := 
{ to_fun := λ m,
    let p := classical.indefinite_description _
        (exists_unique_add_of_is_compl h m) in
    let q := classical.indefinite_description _ p.2 in φ p.1 + ψ q.1,
  map_add' := 
    begin
      intros x y,
      set r := classical.indefinite_description _
        (exists_unique_add_of_is_compl h (x + y)) with hr,
      set s := classical.indefinite_description _ r.2 with hs,
      set rx := classical.indefinite_description _
        (exists_unique_add_of_is_compl h x) with hrx,
      set sx := classical.indefinite_description _ rx.2 with hsx,
      set ry := classical.indefinite_description _
        (exists_unique_add_of_is_compl h y) with hry,
      set sy := classical.indefinite_description _ ry.2 with hsy,
      
      change φ r.1 + ψ s.1 = (φ rx.1 + ψ sx.1) + (φ ry.1 + ψ sy.1), 
      have heq : (rx.1 + ry.1).1 + (sx.1 + sy.1).1 = x + y,
      { simp only [subtype.val_eq_coe, coe_add],
        erw [← add_assoc, add_comm, add_comm ↑↑rx, add_assoc, sx.2.1, 
             ← add_assoc, add_comm ↑↑sy, sy.2.1, add_comm] },
      obtain ⟨h₁, h₂⟩ := s.2.2 (rx + ry) (sx + sy) heq,
      simp_rw [← h₁, ← h₂, linear_map.map_add, add_assoc, 
               ← add_assoc (ψ sx.1), add_comm (ψ sx.1), ← add_assoc], refl,
    end,
  map_smul' := 
    begin
      intros m x,
      set r := classical.indefinite_description _
        (exists_unique_add_of_is_compl h x) with hr,
      set s := classical.indefinite_description _ r.2 with hs,
      set rm := classical.indefinite_description _
        (exists_unique_add_of_is_compl h (m • x)) with hrm,
      set sm := classical.indefinite_description _ rm.2 with hsm,

      change φ rm.1 + ψ sm.1 = m • (φ r.1 +  ψ s.1),
      rw [smul_add, ← linear_map.map_smul, ← linear_map.map_smul],
      obtain ⟨h₁, h₂⟩ := sm.2.2 (m • r.1) (m • s.1) _,
      { rw [h₁, h₂] },
      { simp only [coe_smul, subtype.val_eq_coe, ← smul_add],
        erw s.2.1 }
    end } .

lemma of_is_compl_left_apply {P Q : submodule R M} 
  {φ : P →ₗ[R] M₁} {ψ : Q →ₗ[R] M₁} (h : is_compl P Q) (p : P) : 
  of_is_compl h φ ψ p.1 = φ p :=
begin
  set r := classical.indefinite_description _
    (exists_unique_add_of_is_compl h p) with hr,
  set s := classical.indefinite_description _ r.2 with hs,
  change φ r.1 + ψ s.1 = _,
  obtain ⟨h₁, h₂⟩ := s.2.2 p 0 (add_zero _),
  rw [← h₂, ← h₁, linear_map.map_zero, add_zero]
end  

lemma of_is_compl_right_apply {P Q : submodule R M} 
  {φ : P →ₗ[R] M₁} {ψ : Q →ₗ[R] M₁} (h : is_compl P Q) (q : Q) : 
  of_is_compl h φ ψ q.1 = ψ q :=
begin
  set r := classical.indefinite_description _
    (exists_unique_add_of_is_compl h q) with hr,
  set s := classical.indefinite_description _ r.2 with hs,
  change φ r.1 + ψ s.1 = _,
  obtain ⟨h₁, h₂⟩ := s.2.2 0 q (zero_add _),
  rw [← h₂, ← h₁, linear_map.map_zero, zero_add]
end  

end of_compl

section

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

end

end submodule