import NLS.KdV.HillFreeShiftedMiuraSheets
import NLS.KdV.HillFreeTraceEnergyDerivative
import NLS.ComplexAnalysis.QuadraticEnergyDerivative
import NLS.ZakharovShabat.SourceCriticalRootRatioCollapsed
import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumPath
import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy

/-! The ACTUAL filled discriminant-derivative/root quotient for a free
Hill shifted-Miura realization, off the real frequency axis. The sign is
inherited from the proved free-normalized physical sheet. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem shifted_square_im_ne_zero (z : ℂ) (c : ℝ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    (z^2-(c:ℂ)).im ≠ 0 := by
  simp only [sub_im,ofReal_im,sub_zero,pow_two,mul_im]
  have hp := mul_ne_zero hzr.ne' hzi
  intro he
  apply hp
  linear_combination he/2

theorem deriv_discriminant_shifted_free_miura (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (z : ℂ) (hne : z^2-(c:ℂ) ≠ 0) :
    deriv (canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val))) z =
      (-sin (sqrt (z^2-(c:ℂ)))/sqrt (z^2-(c:ℂ)))*(2*z) := by
  have he : canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val)) =
      fun w => hillHminusDiscriminant 0 (w^2-(c:ℂ)) := by
    funext w
    exact (hillHminusDiscriminant_shifted_miura_square 0 u.val (c:ℂ) w
      (by simpa only [zero_add] using hi)).symm
  have hN : DifferentiableAt ℂ (hillHminusDiscriminant 0) (z^2-(c:ℂ)) :=
    ((analyticOnNhd_hillHminusDiscriminant_joint (z^2-(c:ℂ),0) (mem_univ _)).comp
      (f := fun w : ℂ => (w,(0 : PeriodOneHminusOne))) (analyticAt_id.prod analyticAt_const)).differentiableAt
  rw [he,deriv_comp_quadratic_shift _ z (c:ℂ) hN,
    deriv_hillHminusDiscriminant_free_energy _ hne]

theorem sourceCriticalRootRatioExtension_shifted_free_nonreal
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (n : ℤ) (hgap : sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) n=0)
    (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    sourceCriticalRootRatioExtension (by norm_num) (by norm_num) n (hillMiuraDiagonal u.val) z =
      -I*z/sqrt (z^2-(c:ℂ)) := by
  have hreal : IsRealType (CoeffPair.toMax 2 (hillMiuraDiagonal u.val)) := (hillMiuraRealSource u).property
  have hz := sourceCanonicalRootDomain_of_im_ne_zero (by norm_num) (by norm_num) _ hreal z hzi
  obtain ⟨W,_,hWreal,hE⟩ := exists_global_sourceCriticalRootRatio_analytic_of_zeroGap
    (p := 2) (by norm_num) (by norm_num)
  rw [(hE _ (hWreal hreal) n hgap).2 z hz,
    sourceCanonicalRoot_shifted_free_miura u c hi z hzr hzi]
  have hene : z^2-(c:ℂ) ≠ 0 := fun he =>
    shifted_square_im_ne_zero z c hzr hzi (by rw [he]; rfl)
  rw [deriv_discriminant_shifted_free_miura u c hi z hene]
  have hroot := sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) _ z hz
  rw [sourceCanonicalRoot_shifted_free_miura u c hi z hzr hzi] at hroot
  have hs : sin (sqrt (z^2-(c:ℂ))) ≠ 0 := by
    intro he
    apply hroot
    rw [he,mul_zero]
  have hw : sqrt (z^2-(c:ℂ)) ≠ 0 := fun he => hene (by rw [← complex_sqrt_sq (z^2-(c:ℂ)),he]; simp)
  field_simp [hs,hw]
  simp only [I_sq]
  ring

end NLS.KdV
