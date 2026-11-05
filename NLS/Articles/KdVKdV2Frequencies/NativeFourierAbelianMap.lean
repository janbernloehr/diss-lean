import NLS.Articles.KdVKdV2Frequencies.NativeSignedAbelianCoordinates
import NLS.Articles.KdVKdV2Frequencies.FreeFourierDifferential
import NLS.KdV.HillUnitRealSourceJetUniqueness

/-! # The native physical weighted Abelian map has the exact Fourier derivative -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem native_fourier_derivative
    (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (η : ℝ) (hη : 0 < η) (hZ : AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η))
    (hphysical : ∀ p : RealHillWeightedPotential SpectralWeight.one,
      SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
      Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p)
    (h : Coeff 2) (h0 : h 0 = 0) (j : ℤ) :
    ((fderiv ℂ Z 0) h).val j = (Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h j := by
  let w := hillAbelianTargetWeight SpectralWeight.one
  let ev : WeightedCoeff w 2 →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).comp
    (WeightedCoeff.weightIsometry w 2).toContinuousLinearEquiv.toContinuousLinearMap
  let C := fun u => ev (Z u)
  obtain ⟨W,hW,_,hDW,hWmatch⟩ := exists_hillPhysicalAbelianMap_scalar_fourier_differential j
  let G := fun u => (w j : ℂ)*W u
  have hZd := (hZ 0 (mem_ball_self hη)).differentiableAt
  have hCd : HasFDerivAt C (ev.comp (fderiv ℂ Z 0)) 0 := ev.hasFDerivAt.comp 0 hZd.hasFDerivAt
  have hGd := hW.differentiableAt.hasFDerivAt.const_mul (w j : ℂ)
  let p0 : RealHillWeightedPotential SpectralWeight.one := ⟨0,by intro k;simp⟩
  have ht : Tendsto (fun p : RealHillWeightedPotential SpectralWeight.one =>
      SpectralWeight.one.doubleIndex.toCoeff p.val) (𝓝 p0) (𝓝 (0 : Coeff 2)) := by
    have hc : Continuous (fun p : RealHillWeightedPotential SpectralWeight.one =>
        SpectralWeight.one.doubleIndex.toCoeff p.val) :=
      SpectralWeight.one.doubleIndex.toCoeff.continuous.comp continuous_subtype_val
    simpa only [p0,map_zero] using hc.tendsto p0
  have he : ∀ᶠ p : RealHillWeightedPotential SpectralWeight.one in 𝓝 p0,
      C (SpectralWeight.one.doubleIndex.toCoeff p.val) = G (SpectralWeight.one.doubleIndex.toCoeff p.val) := by
    filter_upwards [ht.eventually (ball_mem_nhds (0 : Coeff 2) hη),hWmatch] with p hp hpmatch
    change (w j : ℂ)*(Z (SpectralWeight.one.doubleIndex.toCoeff p.val)).val j =
      (w j : ℂ)*W (SpectralWeight.one.doubleIndex.toCoeff p.val)
    rw [hphysical p hp,hpmatch]
  have hd := fderiv_eq_of_eventuallyEq_unit_realPotentials C G hCd.differentiableAt hGd.differentiableAt he
  rw [hCd.fderiv,hGd.fderiv] at hd
  have hh := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hd
  change (w j : ℂ)*((fderiv ℂ Z 0) h).val j = (w j : ℂ)*((fderiv ℂ W 0) h) at hh
  exact (mul_left_cancel₀ (w.complex_ne_zero j) hh).trans (hDW h h0)

theorem exists_hillPhysical_native_fourier_abelian_map :
    ∃ η : ℝ, ∃ Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2, ∃ K : ℝ,
      0 < η ∧ 0 < K ∧ AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η) ∧ Z 0 = 0 ∧
      (∀ u ∈ ball (0 : Coeff 2) η, ‖Z u‖ ≤ K*(‖u‖+‖u‖^2) ∧ (Z u).val 0 = 0) ∧
      (∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p) ∧
      ∀ h : Coeff 2, h 0 = 0 → ∀ j : ℤ,
        ((fderiv ℂ Z 0) h).val j = (Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h j := by
  obtain ⟨η,Z,K,hη,hK,hZa,hZ0,hZb,hphysical⟩ := exists_hillPhysical_native_signed_abelian_coordinates
  have hp (p : RealHillWeightedPotential SpectralWeight.one)
      (h : SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η) :
      Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p := by
    apply Subtype.ext
    funext j
    exact (hphysical p h j).trans (by
      rw [hillPhysicalAbelianMap,hillAbelianCoordinateSequence_apply])
  exact ⟨η,Z,K,hη,hK,hZa,hZ0,hZb,hp,native_fourier_derivative Z η hη hZa hp⟩

end NLS.Articles.KdVKdV2Frequencies
