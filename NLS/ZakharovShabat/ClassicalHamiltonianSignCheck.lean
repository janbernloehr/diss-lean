import NLS.ZakharovShabat.ClassicalNLSHamiltonians

/-! # A normalization check at the first problematic even order in Lemma 26.2 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The physical fifth Hamiltonian is nonzero on the constant real-type potential. -/
theorem classicalNLSHamiltonian_constant_one_five : classicalNLSHamiltonian (fun _ => 1) (fun _ => 1) 5 = 2 := by
  have h0 : nlsRiccatiDensity (fun _ => 1) (fun _ => 1) 0 = fun _ => -1 := by
    ext x
    simp
  have h1 : nlsRiccatiDensity (fun _ => 1) (fun _ => 1) 1 = fun _ => 0 := by
    ext x
    simp
  have h2 : nlsRiccatiDensity (fun _ => 1) (fun _ => 1) 2 = fun _ => 1 := by
    ext x
    simp
  have h3 : nlsRiccatiDensity (fun _ => 1) (fun _ => 1) 3 = fun _ => 0 := by
    rw [show 3 = 1+2 by rfl, nlsRiccatiDensity_succ_succ, h2]
    ext x
    simp [Finset.Nat.antidiagonal_succ, h0, h1]
  have h4 : nlsRiccatiDensity (fun _ => 1) (fun _ => 1) 4 = fun _ => -2 := by
    rw [show 4 = 2+2 by rfl, nlsRiccatiDensity_succ_succ, h3]
    ext x
    norm_num [Finset.Nat.antidiagonal_succ, h0, h1, h2]
  simp [classicalNLSHamiltonian, h4, pow_succ]

end NLS.ZakharovShabat
