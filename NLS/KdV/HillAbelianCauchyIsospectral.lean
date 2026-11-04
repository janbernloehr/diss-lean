import NLS.KdV.HillAbelianIsospectralData
import NLS.KdV.HillAbelianFilledQuotient
import NLS.ComplexAnalysis.QuadraticCauchyStationarity

/-! The actual filled off-index Hill Cauchy solution is stationary
on its entire assigned disc in every native isospectral direction.
Analytic quadratic-equation uniqueness includes both endpoints and
collapsed gaps. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem fderiv_offIndexAbelianFilledQuotient_isospectral_eq_zero
    (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0)
    (z : ℂ) (hz : z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) :
    (fderiv ℂ (fun a => P.offIndexAbelianFilledQuotient n m (z,a)) q) h = 0 := by
  let H := P.offIndexAbelianFilledQuotient n m
  let N := P.abelianGapNumerator n m
  let M : PeriodOneHminusOne → ℂ := fun a => sourceStandardRootMidpoint
    (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)
  let G : PeriodOneHminusOne → ℂ := fun a => (canonicalPeriodicGap (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) ((m:ℕ):ℤ))^2
  let u := canonicalPeriodicLeft (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ)
  let v := canonicalPeriodicRight (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ)
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hu : u ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) :=
    D.gap (left_mem_segment ℝ u v)
  have hM : DifferentiableAt ℂ M q :=
    (P.parent.parent.miuraBall.midpoint_analytic ((m:ℕ):ℤ) q
      (P.parent.subset (P.subset hq)).1).differentiableAt
  have hG : DifferentiableAt ℂ G q :=
    (P.parent.parent.miuraBall.dirac_gap_square_analytic ((m:ℕ):ℤ) q
      (P.parent.subset (P.subset hq)).1).differentiableAt
  exact fderiv_quadratic_equation_eq_zero_of_stationary_data H N M G
    (ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) P.source
    isOpen_ball P.source_open (convex_ball _ _).isPreconnected q h hq u v hu
    rfl rfl hM hG (P.fderiv_symmetric_isospectral_eq_zero q hq hr h hiso ((m:ℕ):ℤ))
    (P.analytic_offIndexAbelianFilledQuotient n m hmn)
    (fun a ha w hw => P.offIndexAbelianFilledQuotient_equation n m hmn a ha w hw)
    (fun w hw => P.fderiv_abelianGapNumerator_isospectral_eq_zero n m q hq hr h hiso w hw) z hz

end NLS.KdV.HillProductEquationPatch
