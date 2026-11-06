import NLS.KdV.HillFreeUniformPeriodJacobian
import NLS.ComplexAnalysis.BanachHolomorphicC1
import NLS.ComplexAnalysis.QuantitativeAnalyticInverse

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem norm_hillFreeSupportedPeriodMap_le (n : ℕ) (hn : 1≤n)
    (a : PositiveDeletedCoeff 2 (n : ℤ)) :
    ‖hillFreeSupportedPeriodMap hq hr n hn a‖≤Real.exp ((2/Real.pi^2)*‖a‖)*‖a‖ := by
  change ‖(hillFreeSupportedPeriodMap hq hr n hn a : Coeff 2)‖≤_
  rw [hillFreeSupportedPeriodMap_coe]
  simpa only [Submodule.norm_coe] using norm_hillFreeScaledPeriodSequence_le hq hr n hn (a : Coeff 2)

/-- A common outer-ball bound gives a coordinate-index uniform Lipschitz
constant for the actual free supported-period Jacobians. -/
theorem hillFreeSupportedPeriodMap_uniform_derivative_lipschitz (R : ℝ) (hR : 0<R)
    (n : ℕ) (hn : 1≤n) (x y : PositiveDeletedCoeff 2 (n : ℤ))
    (hx : x∈ball 0 R) (hy : y∈ball 0 R) :
    ‖fderiv ℂ (hillFreeSupportedPeriodMap hq hr n hn) x-
      fderiv ℂ (hillFreeSupportedPeriodMap hq hr n hn) y‖ ≤
        (4*(Real.exp ((2/Real.pi^2)*(4*R))*(4*R))/R^2)*‖x-y‖ := by
  apply norm_fderiv_sub_le_of_holomorphic_ball_bound
    (hillFreeSupportedPeriodMap hq hr n hn) 0 R _ hR
    ((analyticOnNhd_hillFreeSupportedPeriodMap hq hr n hn).differentiableOn.mono (subset_univ _)) _ hy hx
  intro z hz
  have hzR : ‖z‖≤4*R := (show ‖z‖<4*R by simpa only [mem_ball,dist_zero_right] using hz).le
  exact (norm_hillFreeSupportedPeriodMap_le hq hr n hn z).trans
    (mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzR (by positivity))) hzR
      (norm_nonneg _) (Real.exp_nonneg _))

/-- The original free supported-period maps admit analytic inverse charts
with common source and image radii, simultaneously in every coordinate index. -/
theorem exists_hillFreeSupportedPeriodMap_common_analytic_inverse :
    ∃ ρ δ : ℝ, 0<ρ ∧ 0<δ ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ G : PositiveDeletedCoeff 2 (n : ℤ) → PositiveDeletedCoeff 2 (n : ℤ),
        AnalyticOnNhd ℂ G (ball 0 δ) ∧ G 0=0 ∧
        ∀ y∈ball 0 δ, G y∈ball 0 ρ ∧ hillFreeSupportedPeriodMap hq hr n hn (G y)=y ∧
          ∀ x∈ball 0 ρ, hillFreeSupportedPeriodMap hq hr n hn x=y → x=G y := by
  obtain ⟨R,hR,hbound⟩ := exists_hillFreeSupportedPeriodMap_uniform_inverse_bound hq hr
  let L := 4*(Real.exp ((2/Real.pi^2)*(4*R))*(4*R))/R^2
  have hL : 0≤L := by dsimp only [L];positivity
  let ρ := quantitativeInverseJointRadius R 2 L
  let δ := quantitativeInverseImageRadius R 2 L
  refine ⟨ρ,δ,quantitativeInverseJointRadius_pos hR (by norm_num) hL,
    quantitativeInverseImageRadius_pos hR (by norm_num) hL,?_⟩
  intro n hn
  let F := hillFreeSupportedPeriodMap hq hr n hn
  let D := fderiv ℂ F 0
  obtain ⟨S,hDS,hSD,hS⟩ := hbound n hn 0 (by simpa only [norm_zero] using hR.le)
  have hleft : Function.LeftInverse S D := by
    intro x
    have hh := congrArg (fun T : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ) => T x) hSD
    exact hh
  have hright : Function.RightInverse S D := by
    intro x
    have hh := congrArg (fun T : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ) => T x) hDS
    exact hh
  let T := ContinuousLinearEquiv.equivOfInverse D S hleft hright
  have hT : (T : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ))=fderiv ℂ F 0 := rfl
  have hTB : ‖(T.symm : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ))‖≤2 := hS
  have hbij (x : PositiveDeletedCoeff 2 (n : ℤ)) (hx : x∈ball 0 R) :
      Function.Bijective (fderiv ℂ F x) := by
    have hxR : ‖x‖≤R := (show ‖x‖<R by simpa only [mem_ball,dist_zero_right] using hx).le
    obtain ⟨Sx,hDSx,hSxD,_⟩ := hbound n hn x hxR
    exact ContinuousLinearMap.isUnit_iff_bijective.mp ⟨⟨fderiv ℂ F x,Sx,hDSx,hSxD⟩,rfl⟩
  obtain ⟨G,hGa,hG0,hG⟩ := exists_analytic_inverse_on_uniform_ball F 0 R 2 L hR (by norm_num) hL
    ((analyticOnNhd_hillFreeSupportedPeriodMap hq hr n hn).mono (subset_univ _)) T hT hTB
    (fun x hx y hy => hillFreeSupportedPeriodMap_uniform_derivative_lipschitz hq hr R hR n hn x y hx hy) hbij
  have hF0 : F 0=0 := hillFreeSupportedPeriodMap_zero hq hr n hn
  rw [hF0] at hGa hG0 hG
  exact ⟨G,hGa,hG0,hG⟩

end NLS.KdV
