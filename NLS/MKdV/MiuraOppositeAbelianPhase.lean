import NLS.MKdV.MiuraIndependentPhaseKroneckerGenerator
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Source orientation of the independent spectral phase

The phase is the conjugate of the independently constructed Hill Abelian
phase, with no reference to an NLS angle. It has negative physical action
generators at interior finite-gap divisors. The global flow law through
terminal divisors and on arbitrary support remains to be proved.
-/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraNativeOppositeAbelianPhase (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n)
    (a : MiuraRealSobolevSource s) : ℂ :=
  conj (miuraNativeFullAbelianPhase s hs n hn a)

theorem norm_miuraNativeOppositeAbelianPhase (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n)
    (a : MiuraRealSobolevSource s) (hangle : miuraNativeNLSAngularCoordinate s n a ≠ 0) :
    ‖miuraNativeOppositeAbelianPhase s hs n hn a‖ = 1 := by
  rw [miuraNativeOppositeAbelianPhase,norm_conj]
  exact norm_miuraNativeFullAbelianPhase s hs n hn a hangle

theorem norm_miuraNativeOppositeAbelianPhase_le_one (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n)
    (a : MiuraRealSobolevSource s) : ‖miuraNativeOppositeAbelianPhase s hs n hn a‖ ≤ 1 := by
  rw [miuraNativeOppositeAbelianPhase,norm_conj]
  exact norm_miuraNativeFullAbelianPhase_le_one s hs n hn a

theorem miuraNativeOppositeAbelianPhase_closed (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n)
    (a : MiuraRealSobolevSource s) (hangle : miuraNativeNLSAngularCoordinate s n a = 0) :
    miuraNativeOppositeAbelianPhase s hs n hn a = 0 := by
  rw [miuraNativeOppositeAbelianPhase,miuraNativeFullAbelianPhase_closed s hs n hn a hangle,map_zero]

theorem continuousOn_miuraNativeOppositeAbelianPhase (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (miuraNativeOppositeAbelianPhase s hs n hn) {a | miuraNativeNLSAngularCoordinate s n a ≠ 0} :=
  continuous_conj.comp_continuousOn (continuousOn_miuraNativeFullAbelianPhase s hs n hn)

theorem hasDerivAt_miuraNativeOppositeAbelianPhase_actionFlow_finiteGap_generator
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hnF : n-1 ∈ F) (t : ℝ)
    (hclosed : ∀ k, k ∉ F → hillRealGapHalfLength (miuraNativeHillActionCurve s hs a j t).val
      (miuraNativeHillActionCurve s hs a j t).property.1 (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) = 0)
    (hR : ∀ k ∈ F,hillDirichletSheetRoot
      (SpectralWeight.one.toCoeff (miuraNativeHillActionCurve s hs a j t).val)
      (hillDirichletEnergy (miuraNativeHillActionCurve s hs a j t).val
        (miuraNativeHillActionCurve s hs a j t).property.1
        (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) (by omega)) ≠ 0) :
    HasDerivAt (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r))
      (-I*(if j = n then 1 else 0)*miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)) t := by
  have hd := hasDerivAt_miuraNativeFullAbelianPhase_actionFlow_finiteGap_generator s hs a j hj n hn F hnF t hclosed hR
  apply hd.star.congr_deriv
  change conj (I*(if j = n then 1 else 0)*miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)) =
    -I*(if j = n then 1 else 0)*conj (miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t))
  have hδ : conj (if j = n then (1:ℂ) else 0) = if j = n then 1 else 0 := by
    split_ifs <;> simp only [map_one,map_zero]
  simp only [map_mul,conj_I,hδ]

end NLS.MKdV
