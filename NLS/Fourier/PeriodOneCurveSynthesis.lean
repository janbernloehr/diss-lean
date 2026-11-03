import NLS.Fourier.PeriodOneFourierUniqueness
import NLS.Fourier.ContinuousPeriodOneRealization

/-! # Pointwise recovery of a closed periodic interval from its actual coefficients -/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.Fourier

theorem periodOneSobolevSynthesis_eq_curve (a : ScalarDomain 2) (f : Curve ℂ)
    (hend : f ⟨1,by norm_num⟩ = f ⟨0,by norm_num⟩)
    (hcoeff : ∀ n, a.val n = periodOneCoefficient (NLS.LinearVolterra.extend f) n)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)) = NLS.LinearVolterra.extend f x := by
  have hper : NLS.LinearVolterra.extend f 0 = NLS.LinearVolterra.extend f 1 := by
    simpa only [NLS.LinearVolterra.extend,
      projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num)] using hend.symm
  let r := periodOneRepeat (NLS.LinearVolterra.extend f)
  have hc (n : ℤ) : periodOneCoefficient r n = periodOneCoefficient (NLS.LinearVolterra.extend f) n := by
    apply congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 1) ?_) n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact periodOneRepeat_apply ht
  have he := periodOneSobolevSynthesis_eq_of_coefficients a r
    (continuous_periodOneRepeat _ (continuous_extend f) hper) (periodOneRepeat_periodic _)
    (fun n => (hcoeff n).trans (hc n).symm)
  rw [congrFun he x]
  by_cases hp : 0 < x
  · exact periodOneRepeat_apply ⟨hp,hx.2⟩
  · have hzero : x = 0 := le_antisymm (le_of_not_gt hp) hx.1
    subst x
    calc
      r 0 = r 1 := by simpa only [zero_add] using (periodOneRepeat_periodic (NLS.LinearVolterra.extend f) 0).symm
      _ = NLS.LinearVolterra.extend f 1 := periodOneRepeat_apply (by norm_num)
      _ = NLS.LinearVolterra.extend f 0 := hper.symm

end NLS.Fourier
