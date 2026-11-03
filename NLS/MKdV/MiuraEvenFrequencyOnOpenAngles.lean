import NLS.MKdV.MiuraNativeHamiltonianFactorDifferential
import NLS.MKdV.MiuraThetaNativeActionDifferential

/-! # The actual all-order NLS/Hill frequency comparison on the open-angle domain

The NLS side is the actual original S_(2s+2) angle bracket on H^(s+1).
The Hill side is the raw positive-action derivative of any independently
constructed native K_(s+1) normal form. All other actions may be closed.
The extension to the sharp H^s domain is a separate theorem.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraOriginalEvenNLSAngleFrequency_eq_Hill_frequency (s : ℕ)
    (D : MiuraNativeHamiltonianActionData s) (a : MiuraRealSobolevSource (s+1))
    (n : ℕ) (hn : 1 ≤ n)
    (hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) :
    miuraOriginalEvenNLSAngleFrequency s a n hgap =
      D.frequency (n : ℤ) (miuraNativeActionMeanMap s (miuraRealSobolevLower s a).val) := by
  rw [miuraOriginalEvenNLSAngleFrequency_eq_native_cotangent]
  change -fderiv ℂ (nativeMiuraHillHamiltonian s) (miuraRealSobolevLower s a).val
    (miuraThetaNativeGardnerDirection s a n hgap) = _
  rw [D.fderiv_recovery,ContinuousLinearMap.comp_apply,
    miuraThetaNativeActionMean_differential s a n hn hgap,map_neg,neg_neg]
  rfl

end NLS.MKdV
