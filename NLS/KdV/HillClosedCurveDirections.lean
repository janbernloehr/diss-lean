import NLS.FunctionalAnalysis.ClosedUnitCurvePeriodic
import NLS.KdV.HillRoughScalarEquation
import NLS.KdV.HillPhysicalDirectionPairing
import NLS.FunctionalAnalysis.UnitComplexCurvePairing

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem hillPhysicalDirection_lower_ae (h : Coeff 2) :
    (fun x : ℝ => (hillPhysicalDirection h).ofLp.2 x)=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      Fourier.circlePullback (Fourier.l2Synthesis (-h)) := by
  filter_upwards [physicalRestrictionL2_representative (hillFirstOrderDirection h)] with x hx
  exact congrArg Prod.snd hx

theorem hillPhysicalDirection_continuous_coefficients (Q : C(AddCircle (2 : ℝ),ℂ)) :
    (fun x : ℝ => -(hillPhysicalDirection (SpectralWeight.one.toCoeff
      (hillContinuousCoefficients Q))).ofLp.2 x)=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        NLS.LinearVolterra.extend (hillUnitPotentialCurve Q) := by
  have hdir := hillPhysicalDirection_lower_ae (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))
  rw [map_neg,l2Synthesis_hillContinuousCoefficients] at hdir
  have hQ := Fourier.circle_ae_pullback
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle Q)
  have hN := Fourier.circle_ae_pullback (Lp.coeFn_neg (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q))
  rw [Filter.EventuallyEq,ae_restrict_iff' measurableSet_Ioc] at hQ hN
  have hQ1 := (ae_restrict_iff' measurableSet_Ioc).mpr hQ
  have hN1 := (ae_restrict_iff' measurableSet_Ioc).mpr hN
  have hQ2 := hQ1.filter_mono (ae_mono (Measure.restrict_mono
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ)≤2)) le_rfl))
  have hN2 := hN1.filter_mono (ae_mono (Measure.restrict_mono
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ)≤2)) le_rfl))
  filter_upwards [hdir,hQ2,hN2,ae_restrict_mem measurableSet_Ioc] with x hx hxQ hxN hxi
  have hx2 : x∈Ioc (0 : ℝ) 2 := ⟨hxi.1,by linarith [hxi.2]⟩
  change -(hillPhysicalDirection (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))).ofLp.2 x=_
  rw [hx]
  change -((-(ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q)) (x : AddCircle (2 : ℝ)))=_
  rw [hxN]
  dsimp only [Pi.neg_apply]
  rw [hxQ,neg_neg]
  dsimp only [NLS.LinearVolterra.extend,hillUnitPotentialCurve,ContinuousMap.coe_mk]
  rw [projIcc_of_mem _ (show x∈Icc (0 : ℝ) 1 from ⟨hxi.1.le,hxi.2⟩)]

/-- A genuine unit-weight, period-one Hill source direction obtained
from a closed continuous physical unit curve. -/
def hillClosedCurveCoefficients (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) : WeightedCoeff SpectralWeight.one.toWeight 2 :=
  hillContinuousCoefficients (closedUnitCurvePeriodTwo f hf)

theorem hillClosedCurveCoefficients_mem_even (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) :
    SpectralWeight.one.toCoeff (hillClosedCurveCoefficients f hf)∈Coeff.paritySubspace 0 :=
  hillContinuousCoefficients_mem_even (closedUnitCurvePeriodTwo f hf) (periodic_closedUnitCurvePeriodTwo f hf)

theorem hillClosedCurveCoefficients_physical (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) :
    (fun x : ℝ => -(hillPhysicalDirection (SpectralWeight.one.toCoeff
      (hillClosedCurveCoefficients f hf))).ofLp.2 x)=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        NLS.LinearVolterra.extend f := by
  have hh := hillPhysicalDirection_continuous_coefficients (closedUnitCurvePeriodTwo f hf)
  apply hh.trans
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  dsimp only [NLS.LinearVolterra.extend,hillUnitPotentialCurve,ContinuousMap.coe_mk]
  rw [projIcc_of_mem _ (show x∈Icc (0 : ℝ) 1 from ⟨hx.1.le,hx.2⟩)]
  change closedUnitCurvePeriodic f hf x=f ⟨x,hx.1.le,hx.2⟩
  simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show x∈Icc (0 : ℝ) 1 from ⟨hx.1.le,hx.2⟩)] using
    closedUnitCurvePeriodic_eq f hf x hx

theorem hillClosedCurveCoefficients_pairing (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) (v : Curve ℂ) :
    hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff (hillClosedCurveCoefficients f hf)) v=
      unitComplexCurvePairing f v := by
  rw [hillPhysicalDirectionPairing_apply]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [hillClosedCurveCoefficients_physical f hf] with x hx
  rw [hx]
  rfl

theorem hillClosedCurveCoefficients_zero (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) :
    (hillClosedCurveCoefficients f hf).val 0=∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend f x := by
  let Q := closedUnitCurvePeriodTwo f hf
  change (hillContinuousCoefficients Q).val 0=_
  rw [hillContinuousCoefficients_apply,← Fourier.periodTwoCoefficient_circle]
  have he := Fourier.periodTwoCoefficient_periodic_even
    (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) (periodic_closedUnitCurvePeriodTwo f hf)
    ((Q.continuous.comp (by fun_prop)).intervalIntegrable 0 1) 0
  rw [mul_zero] at he
  rw [he,Fourier.periodOneCoefficient,fourierCoeffOn_eq_integral]
  simp only [sub_zero,div_one,one_smul,neg_zero,fourier_zero]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact closedUnitCurvePeriodic_eq f hf x hx

end NLS.KdV
