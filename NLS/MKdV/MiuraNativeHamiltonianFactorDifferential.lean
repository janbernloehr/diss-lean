import NLS.MKdV.MiuraNativeHamiltonianFrequencies
import NLS.MKdV.MiuraNativeActionMeanDifferential
import NLS.ComplexAnalysis.FDerivRealFormUnique

/-! # The chain rule for independent native Hill action normal forms

Real recovery and the spanning physical real form identify the full
complex differential. This proves the operator identity before evaluating
on any angular direction, with no canonical-coordinate assumption.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV.MiuraNativeHamiltonianActionData

theorem fderiv_recovery {s : ℕ} (D : MiuraNativeHamiltonianActionData s)
    (a : MiuraRealSobolevSource s) :
    fderiv ℂ (nativeMiuraHillHamiltonian s) a.val =
      (fderiv ℂ D.hamiltonian (miuraNativeActionMeanMap s a.val)).comp
        (fderiv ℂ (miuraNativeActionMeanMap s) a.val) := by
  have hw : ∀ k : ℤ, Weight.sobolev (s : ℝ) (-k) = Weight.sobolev (s : ℝ) k := by intro k; simp
  have hspan (h : ScalarSobolev s) : ∃ x y : MiuraRealSobolevSource s, h = x.val+I • y.val :=
    ⟨WeightedCoeff.physicalRealPart _ hw h,WeightedCoeff.physicalRealPart _ hw ((-I) • h),
      WeightedCoeff.physicalRealPart_complex_decomp _ hw h⟩
  have hd := (D.analytic _ (D.contains a)).differentiableAt.hasFDerivAt.comp a.val
    (analyticAt_miuraNativeActionMeanMap s a).differentiableAt.hasFDerivAt
  have he := NLS.ComplexAnalysis.fderiv_eq_of_real_form_agreement (MiuraRealSobolevSource s) hspan
    (fun b => D.hamiltonian (miuraNativeActionMeanMap s b)) (nativeMiuraHillHamiltonian s)
    a hd.differentiableAt (analyticAt_nativeMiuraHillHamiltonian s a.val).differentiableAt
    (fun b => by rw [D.recovery b,miuraSpectralHillHamiltonian_eq_native])
  rw [← he]
  exact hd.fderiv

end NLS.MKdV.MiuraNativeHamiltonianActionData
