import linear_algebra.basic 

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]

def foo (P Q : submodule R M) (f : P.quotient ≃ₗ[R] Q) : Q.quotient ≃ₗ[R] P := 
begin
  sorry
end