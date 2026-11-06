import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForward
import NLS.KdV.HillMiuraGroundFiniteGap
import NLS.KdV.HillMiuraGroundTargetBound
import NLS.KdV.HillAbelianCoordinateFactor

/-! # The actual ground energy bounded by the SAME global weak forward target

For original physical finite-gap sources, the normalized factor has
actual spectral finite-gap support. Exact original action calibration
then bounds its energy by the Hilbert norm of D.positive itself.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem positive_physical_action_norm (D : GlobalRoughAbelianForwardData)
    (p : RealPeriodOneHillPotential) (n : ℕ) (hn : 0 < n) :
    hillRealGapIntegral p.val p.property.1 p.property.2 n 0 =
      (1+(n : ℝ))*‖D.positive (hillOriginalHminusSource p.val) (n : ℤ)‖^2 := by
  have hp := D.positive_physical p ⟨n,hn⟩
  change D.positive (hillOriginalHminusSource p.val) (n : ℤ) =
    hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn/
      (Real.sqrt (1+(n : ℝ)) : ℂ) at hp
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by simp
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro j; simp
  have hs : ‖(Real.sqrt (1+(n : ℝ)) : ℂ)‖^2 = 1+(n : ℝ) := by
    rw [norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by positivity)]
  rw [hp,norm_div,div_pow,hs,norm_sq_hillDirichletAbelianCoordinate _ _ _ h0q h0r n hn]
  field_simp

theorem ground_energy_le_positive_norm_of_physical_finiteGap (D : GlobalRoughAbelianForwardData)
    (p : RealPeriodOneHillPotential) (hm : (hillOriginalHminusSource p.val).val 0 = 0)
    (N : ℕ) (hN : 1 ≤ N)
    (hc : ∀ n : ℕ, N ≤ n → hillRealLabels p.val p.property.1 p.property.2 (2*n) =
      hillRealLabels p.val p.property.1 p.property.2 (2*n-1)) :
    -hillHminusLowestRealRoot (hillOriginalHminusSource p.val) (hillOriginalHminusSource_real p.val p.property.2) ≤
      (2/Real.pi)*‖D.positive (hillOriginalHminusSource p.val)‖^2 := by
  let q := hillOriginalHminusSource p.val
  have hq := hillOriginalHminusSource_real p.val p.property.2
  have hclosed : ∀ n : ℕ, N ≤ n → hillHminusRealLabels q hq (2*n) = hillHminusRealLabels q hq (2*n-1) := by
    rw [hillHminusRealLabels_original_source p]
    exact hc
  obtain ⟨u,hu,hi,hn,hf,_hb⟩ := exists_finiteGap_ground_factor_with_energy_bound q hq hm N hN hclosed
  rw [←hn]
  exact hillMiura_finiteGap_energy_le_positive_target_norm p u _ hu hi hf (D.positive q)
    (D.positive_physical_action_norm p)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
