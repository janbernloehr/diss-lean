import NLS.Articles.KdVKdV2Frequencies.ActualNativeJacobianUnit
import NLS.Articles.KdVKdV2Frequencies.ActualRoughFourierDifferential
import NLS.KdV.HillHminusAbelianDerivative
import NLS.ComplexAnalysis.AnalyticJacobianInjectivity

/-! # ONE actual weak Jacobian neighborhood before all native orders -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- The GIVEN actual physical weak map has injective mean-zero Jacobians
on ONE complex normalized rough ball, before any stronger Sobolev order. -/
theorem exists_actual_weak_jacobian_injective_ball
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) :
    ∃ δ : ℝ, 0<δ ∧ δ≤η ∧ ∀ a∈ball (0 : DeletedCoeff 2 0) δ,
      WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a∈ball (0 : PeriodOneHminusOne) η ∧
      DifferentiableAt ℂ (weakMeanZeroAbelianMap Z) a ∧
      Function.Injective (fderiv ℂ (weakMeanZeroAbelianMap Z) a) := by
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  let P := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
  have hLa (a : DeletedCoeff 2 0) (ha : a∈ball (0 : DeletedCoeff 2 0) η) :
      L a∈ball (0 : PeriodOneHminusOne) η := by
    simpa only [L,mem_ball_zero_iff,WeightedCoeff.meanZeroWeightedLift_norm] using ha
  have hFa : AnalyticOnNhd ℂ (weakMeanZeroAbelianMap Z) (ball (0 : DeletedCoeff 2 0) η) := by
    intro a ha
    exact (P.analyticAt _).comp ((hZa (L a) (hLa a ha)).comp (L.analyticAt a))
  have hu : IsUnit (fderiv ℂ (weakMeanZeroAbelianMap Z) 0) := by
    change IsUnit (fderiv ℂ (WeightedCoeff.meanZeroWeightedMap (Weight.sobolev (-1/2))
      (fun u => Z ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm u))) 0)
    exact isUnit_fderiv_meanZeroHminusAbelianMap Z (hZa 0 (mem_ball_self hη)).differentiableAt
      (actual_rough_abelian_fourier_differential η hη Z hZa hphys)
  obtain ⟨V,hV,h0V,hVU,hVI⟩ := NLS.ComplexAnalysis.exists_open_injective_fderiv
    (weakMeanZeroAbelianMap Z) (ball (0 : DeletedCoeff 2 0) η) isOpen_ball hFa 0 (mem_ball_self hη) hu
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  let δ := min η ε
  have hδ : 0<δ := lt_min hη hε
  have hδV : ball (0 : DeletedCoeff 2 0) δ⊆V :=
    fun _ ha => hεV (ball_subset_ball (min_le_right _ _) ha)
  refine ⟨δ,hδ,min_le_left _ _,?_⟩
  intro a ha
  exact ⟨hLa a (hVU (hδV ha)),(hFa a (hVU (hδV ha))).differentiableAt,hVI a (hδV ha)⟩

end NLS.Articles.KdVKdV2Frequencies
