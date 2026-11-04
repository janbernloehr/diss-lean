import NLS.KdV.HillAbelianIsospectralData
import NLS.KdV.HillOnIndexAbelianFilledRemainder
import NLS.ComplexAnalysis.QuadraticCauchyStationarity

/-! The actual diagonal remainder, whose equation retains the
nonzero diagonal period by subtracting i, is stationary throughout
the assigned disc in every native isospectral direction. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem fderiv_onIndexAbelianFilledRemainder_isospectral_eq_zero
    (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0)
    (z : ℂ) (hz : z ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ))) :
    (fderiv ℂ (fun a => P.onIndexAbelianFilledRemainder n (z,a)) q) h = 0 := by
  let H := P.onIndexAbelianFilledRemainder n
  let N : ℂ × PeriodOneHminusOne → ℂ := fun t => P.abelianGapNumerator n n t-I
  let M : PeriodOneHminusOne → ℂ := fun a => sourceStandardRootMidpoint
    (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)
  let G : PeriodOneHminusOne → ℂ := fun a => (canonicalPeriodicGap (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2
  let u := canonicalPeriodicLeft (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ)
  let v := canonicalPeriodicRight (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ)
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((n:ℕ):ℤ)
    (P.centers ((n:ℕ):ℤ)) (P.radii ((n:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hu : u ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) := D.gap (left_mem_segment ℝ u v)
  have hM : DifferentiableAt ℂ M q :=
    (P.parent.parent.miuraBall.midpoint_analytic ((n:ℕ):ℤ) q (P.parent.subset (P.subset hq)).1).differentiableAt
  have hG : DifferentiableAt ℂ G q :=
    (P.parent.parent.miuraBall.dirac_gap_square_analytic ((n:ℕ):ℤ) q (P.parent.subset (P.subset hq)).1).differentiableAt
  apply fderiv_quadratic_equation_eq_zero_of_stationary_data H N M G
    (ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ))) P.source
    isOpen_ball P.source_open (convex_ball _ _).isPreconnected q h hq u v hu rfl rfl hM hG
    (P.fderiv_symmetric_isospectral_eq_zero q hq hr h hiso ((n:ℕ):ℤ))
    (P.analytic_onIndexAbelianFilledRemainder n)
    (fun a ha w hw => P.onIndexAbelianFilledRemainder_equation n a ha w hw) _ z hz
  intro w hw
  have hd := (((P.analytic_abelianGapNumerator_on_patch n n (w,q)
    ⟨ball_subset_closedBall hw,hq⟩).comp
      (f := fun a : PeriodOneHminusOne => (w,a)) (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt).sub_const I
  change HasFDerivAt (fun a => N (w,a)) _ q at hd
  rw [hd.fderiv]
  exact P.fderiv_abelianGapNumerator_isospectral_eq_zero n n q hq hr h hiso w hw

end NLS.KdV.HillProductEquationPatch
