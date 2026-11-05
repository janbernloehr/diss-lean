import NLS.KdV.HillMiuraFiniteGapProfile
import NLS.MKdV.MiuraHierarchyHamiltonians

/-! The actual finite-gap diagonal hierarchy has exactly the original
L2 squared norm at order one and zero at every positive even order. -/
noncomputable section
open Complex NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

theorem sourceFiniteGapNLSHamiltonian_hillMiura_one (u : PeriodOneRealL2)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf 1=
      ((‖u.val‖^2:ℝ):ℂ) := by
  rw [sourceFiniteGapNLSHamiltonian_hillMiura_eq_classical,classicalNLSHamiltonian_one]
  simpa only [pow_two] using integral_sq_hillMiuraFiniteGapProfile u hf

theorem sourceFiniteGapNLSHamiltonian_hillMiura_even (u : PeriodOneRealL2)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (m : ℕ) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf (2*m+2)=0 := by
  rw [sourceFiniteGapNLSHamiltonian_hillMiura_eq_classical]
  exact classicalNLSHamiltonian_even_diagonal_eq_zero _
    (contDiff_hillMiuraFiniteGapProfile u hf) (periodic_hillMiuraFiniteGapProfile u hf) m

end NLS.KdV
