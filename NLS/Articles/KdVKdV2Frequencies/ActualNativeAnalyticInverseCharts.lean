import NLS.Articles.KdVKdV2Frequencies.ActualAllNativeJacobianUnits

/-! # Actual native analytic inverse charts at EVERY eligible real base -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- A local analytic diffeomorphism of the literal native mean-zero
charts of the SAME actual weak coordinate map. Its inverse is analytic
on an OPEN target neighborhood of the actual image of the supplied base. -/
def NativeAbelianAnalyticInverseAt (η : ℝ)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (t : ℝ) (ht : 0≤t) (a : DeletedCoeff 2 0) : Prop :=
  ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧
    WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a∈V ∧
    ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
      AnalyticOnNhd ℂ g V ∧
      (∀ p∈V, periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) η ∧
        WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (g p)=Z (periodOneSobolevImageInclusion t ht p)) ∧
      ∃ P : OpenPartialHomeomorph (DeletedCoeff 2 0) (DeletedCoeff 2 0),
        (P : DeletedCoeff 2 0 → DeletedCoeff 2 0)=nativeMeanZeroAbelianMap t g ∧
        a∈P.source ∧
        P.source⊆(WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))) ⁻¹' V ∧
        AnalyticOnNhd ℂ (nativeMeanZeroAbelianMap t g) P.source ∧ AnalyticOnNhd ℂ P.symm P.target

/-- ONE common rough ball before ALL native orders and EVERY eligible
real mean-zero base has actual complex analytic inverse charts. -/
def HasAllNativeAnalyticInverseCharts (η : ℝ)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2) : Prop :=
  ∃ ρ : ℝ, 0<ρ ∧ ρ≤η ∧ ∀ t : ℝ, ∀ ht : 0≤t, ∀ a : DeletedCoeff 2 0,
    IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)) →
    periodOneSobolevImageInclusion t ht (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)
      ∈ball (0 : PeriodOneHminusOne) ρ → NativeAbelianAnalyticInverseAt η Z t ht a

/-- Actual native Jacobian invertibility gives actual analytic inverse
charts at EVERY eligible real base, retaining the SAME native restriction. -/
theorem HasAllNativeJacobianUnits.analytic_inverse_charts
    {η : ℝ} {Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2}
    (h : HasAllNativeJacobianUnits η Z) : HasAllNativeAnalyticInverseCharts η Z := by
  obtain ⟨ρ,hρ,hρη,hunits⟩ := h
  refine ⟨ρ,hρ,hρη,?_⟩
  intro t ht a hreal ha
  obtain ⟨V,hV,haV,_C,g,_hC,hga,hcomm,hu⟩ := hunits t ht a hreal ha
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))
  let Q := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (t-1/2))
  let U := L ⁻¹' V
  have hU : IsOpen U := hV.preimage L.continuous
  have hf : AnalyticOnNhd ℂ (nativeMeanZeroAbelianMap t g) U := by
    intro b hb
    exact (Q.analyticAt _).comp ((hga (L b) hb).comp (L.analyticAt b))
  obtain ⟨P,hP,haP,hPU,hPa,hPia⟩ := NLS.ComplexAnalysis.exists_analytic_openPartialHomeomorph hU hf haV hu
  exact ⟨V,hV,haV,g,hga,fun p hp => ⟨(hcomm p hp).1,(hcomm p hp).2.2⟩,P,hP,haP,hPU,hPa,hPia⟩

/-- ANY GIVEN actual signed physical map has genuine native complex
analytic inverse charts at ALL eligible real bases in ONE rough ball,
for EVERY order s>=-1, in the exact source/target mean-zero weight charts. -/
theorem exists_actual_all_native_analytic_inverse_charts
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) :
    HasAllNativeAnalyticInverseCharts η Z :=
  (exists_actual_all_native_jacobian_units η hη Z hZa hphys).analytic_inverse_charts

end NLS.Articles.KdVKdV2Frequencies
