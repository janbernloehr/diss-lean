import NLS.ZakharovShabat.ClassicalNLSHamiltonians

/-! # Field rescaling in the actual Riccati recurrence

The proof of H.1 uses u_k(a,c*b)=c*u_k(c*a,b). Recurrence uniqueness
proves the identity directly, including c=0, without division or any
smoothness assumption. Integrating yields the physical Hamiltonian identity.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- Appendix H's field-rescaling identity, including scalar zero, at every order. -/
theorem nlsRiccatiDensity_field_rescaling (a b : ℝ → ℂ) (c : ℂ) (n : ℕ) :
    nlsRiccatiDensity a (c • b) n = c • nlsRiccatiDensity (c • a) b n := by
  have hu := nlsRiccatiDensity_unique a (c • b)
    (fun k => c • nlsRiccatiDensity (c • a) b k)
    (by ext x; simp)
    (by
      rw [nlsRiccatiDensity_one,nlsRiccatiDensity_zero]
      ext x
      simp [deriv_const_smul_field])
    (by
      intro k
      rw [nlsRiccatiDensity_succ_succ]
      ext x
      simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,Pi.mul_apply,
        Finset.sum_apply,deriv_const_smul_field,smul_eq_mul,mul_add,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      ring)
  exact (congrFun hu n).symm

/-- Moving a common scalar from the second field to the first preserves each physical Hamiltonian. -/
theorem classicalNLSHamiltonian_field_rescaling (a b : ℝ → ℂ) (c : ℂ) (k : ℕ) :
    classicalNLSHamiltonian a (c • b) k = classicalNLSHamiltonian (c • a) b k := by
  cases k with
  | zero => rfl
  | succ n =>
    simp only [classicalNLSHamiltonian,nlsRiccatiDensity_field_rescaling,Pi.smul_apply,smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    ring

end NLS.ZakharovShabat
