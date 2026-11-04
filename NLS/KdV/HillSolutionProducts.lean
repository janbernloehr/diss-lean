import NLS.KdV.HillGradientSecondRegularity
import NLS.ComplexAnalysis.ScalarHillProductPairing

/-! # Actual products of two rough scalar Hill solutions -/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillSolutionProductCurve (q : Coeff 2) (E : ℂ) (v w : ℂ × ℂ) : Curve ℂ :=
  ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2FrequencyStateCurve q (Complex.sqrt E) v))*
    ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2FrequencyStateCurve q (Complex.sqrt E) w))

def hillSolutionProductSpatialCurve (q : Coeff 2) (E : ℂ) (v w : ℂ × ℂ) : Curve ℂ :=
  ((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp (hillL2FrequencyStateCurve q (Complex.sqrt E) v))*
    ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2FrequencyStateCurve q (Complex.sqrt E) w))+
  ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2FrequencyStateCurve q (Complex.sqrt E) v))*
    ((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp (hillL2FrequencyStateCurve q (Complex.sqrt E) w))

def hillSolutionProductSecond (q : Coeff 2) (E : ℂ) (v w : ℂ × ℂ) (x : ℝ) : ℂ :=
  2*(extend (hillL2FrequencyStateCurve q (Complex.sqrt E) v) x).2*
      (extend (hillL2FrequencyStateCurve q (Complex.sqrt E) w) x).2+
    2*(hillIntervalPotential q x-E)*(extend (hillL2FrequencyStateCurve q (Complex.sqrt E) v) x).1*
      (extend (hillL2FrequencyStateCurve q (Complex.sqrt E) w) x).1

theorem absolutelyContinuousOnInterval_hillSolutionProductCurve (q : Coeff 2) (E : ℂ) (v w : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (extend (hillSolutionProductCurve q E v w)) 0 1 := by
  have hv := absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_hillStateCurve q (Complex.sqrt E) v)
    (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hw := absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_hillStateCurve q (Complex.sqrt E) w)
    (ContinuousLinearMap.fst ℝ ℂ ℂ)
  convert! hv.smul hw using 1

theorem absolutelyContinuousOnInterval_hillSolutionProductSpatialCurve (q : Coeff 2) (E : ℂ) (v w : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (extend (hillSolutionProductSpatialCurve q E v w)) 0 1 := by
  have hv := absolutelyContinuousOnInterval_hillStateCurve q (Complex.sqrt E) v
  have hw := absolutelyContinuousOnInterval_hillStateCurve q (Complex.sqrt E) w
  have hvf := absolutelyContinuousOnInterval_clm hv (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hvd := absolutelyContinuousOnInterval_clm hv (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hwf := absolutelyContinuousOnInterval_clm hw (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hwd := absolutelyContinuousOnInterval_clm hw (ContinuousLinearMap.snd ℝ ℂ ℂ)
  convert! (hvd.smul hwf).add (hvf.smul hwd) using 1

theorem ae_hasDerivAt_hillSolutionProductCurve (q : Coeff 2) (E : ℂ) (v w : ℂ × ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (hillSolutionProductCurve q E v w))
        (extend (hillSolutionProductSpatialCurve q E v w) x) x := by
  filter_upwards [ae_hasDerivAt_hillL2FrequencyStateCurve_fst q (Complex.sqrt E) v,
    ae_hasDerivAt_hillL2FrequencyStateCurve_fst q (Complex.sqrt E) w] with x hv hw
  exact hv.mul hw

theorem ae_hasDerivAt_hillSolutionProductSpatialCurve (q : Coeff 2) (E : ℂ) (v w : ℂ × ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (hillSolutionProductSpatialCurve q E v w))
        (hillSolutionProductSecond q E v w x) x := by
  filter_upwards [ae_hasDerivAt_hillL2FrequencyStateCurve_fst q (Complex.sqrt E) v,
    ae_hasDerivAt_hillL2FrequencyStateCurve_snd q (Complex.sqrt E) v,
    ae_hasDerivAt_hillL2FrequencyStateCurve_fst q (Complex.sqrt E) w,
    ae_hasDerivAt_hillL2FrequencyStateCurve_snd q (Complex.sqrt E) w] with x hvf hvd hwf hwd
  rw [complex_sqrt_sq] at hvd hwd
  convert! (hvd.mul hwf).add (hvf.mul hwd) using 1
  dsimp only [hillSolutionProductSecond]
  ring

theorem memLp_hillSolutionProductSecond (q : Coeff 2) (E : ℂ) (v w : ℂ × ℂ) :
    MemLp (hillSolutionProductSecond q E v w) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  memLp_hillProductSecond (hillIntervalPotential q) E _ _ (memLp_hillIntervalPotential q)

end NLS.KdV
