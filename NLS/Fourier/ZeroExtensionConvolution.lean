import NLS.Fourier.FoldedSobolev
import NLS.Fourier.IntervalL2Realization
import NLS.Fourier.PhysicalConvolution

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal Classical

namespace NLS.Fourier



/-- A summable sequence of actual half coefficients synthesizes the original
function on the first half and zero on the second half, almost everywhere. -/
theorem continuousSynthesis_halfCoefficients_eq_zeroExtension_ae
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (a : Coeff 1) (ha : ∀ k : ℤ, a k = halfCoefficient f k) :
    (fun x : ℝ => continuousSynthesis a (x : AddCircle (2 : ℝ)))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)] folded 0 f (fun _ => 0) := by
  let F : ℝ → ℂ := fun x => continuousSynthesis a (x : AddCircle (2 : ℝ))
  let Z := folded 0 f (fun _ => 0)
  have hF : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 2)) :=
    memLp_two_interval ((continuousSynthesis a).continuous.comp (by fun_prop)) 0 2 (by norm_num)
  have hZ : MemLp Z 2 (volume.restrict (Ioc (0 : ℝ) 2)) :=
    memLp_folded_of_memLp 0 hf (memLp_const (0 : ℂ))
  have hfi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.integrable (by norm_num))
  have hcoeff : periodTwoL2Coefficients F hF = periodTwoL2Coefficients Z hZ := by
    ext k
    rw [periodTwoL2Coefficients_apply,periodTwoL2Coefficients_apply]
    change periodTwoCoefficient F k = periodTwoCoefficient (folded 0 f (fun _ => 0)) k
    rw [periodTwoCoefficient_folded_of_intervalIntegrable 0 hfi (intervalIntegrable_const) k,
      zero_mul,add_zero]
    exact (periodTwoCoefficient_continuousSynthesis a k).trans (ha k)
  have hleft := circlePullback_periodTwoL2Coefficients F hF
  rw [hcoeff] at hleft
  exact hleft.symm.trans (circlePullback_periodTwoL2Coefficients Z hZ)

/-- Multiplication of a rough period-two potential by a zero-extended
function has exactly the original convolution coefficients. -/
theorem convolution_halfCoefficients_eq_physical_product
    (q : Coeff 2) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (a : Coeff 1) (ha : ∀ k : ℤ, a k = halfCoefficient f k) (k : ℤ) :
    Coeff.convolution q a k =
      halfCoefficient (fun x => circlePullback (l2Synthesis q) x*f x) k := by
  have hreal := continuousSynthesis_halfCoefficients_eq_zeroExtension_ae f hf a ha
  have hprod := circlePullback_circleMul (continuousSynthesis a) (l2Synthesis q)
  rw [circleMul_continuousSynthesis] at hprod
  have hfull : circlePullback (l2Synthesis (Coeff.convolution q a))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)]
        folded 0 (fun x => circlePullback (l2Synthesis q) x*f x) (fun _ => 0) := by
    filter_upwards [hprod,hreal] with x hx hr
    rw [hx,hr]
    dsimp only [folded]
    split_ifs <;> simp [mul_comm]
  have hq := (memLp_circlePullback (l2Synthesis q)).mono_measure
    (Measure.restrict_mono (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2)) (le_refl volume))
  have hQf : IntervalIntegrable (fun x => circlePullback (l2Synthesis q) x*f x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hq.integrable_mul hf)
  have he := congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 2) hfull) k
  rw [← periodTwoCoefficient_eq_fourierCoeffOn,← periodTwoCoefficient_eq_fourierCoeffOn,
    periodTwoCoefficient_circlePullback,fourierCoeff_l2Synthesis,
    periodTwoCoefficient_folded_of_intervalIntegrable 0 hQf intervalIntegrable_const k,
    zero_mul,add_zero] at he
  exact he

end NLS.Fourier
