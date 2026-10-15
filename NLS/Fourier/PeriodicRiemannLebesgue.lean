import NLS.Fourier.PeriodicFourierLebesgueEndpoints
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Topology.Instances.ZMultiples

/-!
# Periodic Riemann–Lebesgue decay

Normalized interval Fourier coefficients vanish at both ends of the integer
frequency axis. Thus every interval L¹ function has Fourier truncations
converging in the original FL∞ norm. Point evaluation cannot be represented by
an interval L¹ function. This proves the decay assertion in Remark A.6;
non-surjectivity of L¹ → c₀ is a separate assertion.
-/

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal FourierTransform
namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]

/-- Extension by zero identifies the normalized coefficient with a real Fourier integral. -/
theorem intervalFourierCoefficient_eq_restrictedFourier (f : ℝ → ℂ) (n : ℤ) :
    intervalFourierCoefficient L f n = (L:ℂ)⁻¹ *
      ∫ v : ℝ, Real.fourierChar (-(v*((n:ℝ)/L))) • (Ioc (0:ℝ) L).indicator f v := by
  have he : (fun v : ℝ => Real.fourierChar (-(v*((n:ℝ)/L))) • (Ioc (0:ℝ) L).indicator f v) =
      (Ioc (0:ℝ) L).indicator (fun v => f v*wave (-n) ((2/L)*v)) := by
    funext v
    by_cases hv : v ∈ Ioc (0:ℝ) L
    · simp only [indicator_of_mem hv,Circle.smul_def,Real.fourierChar_apply,smul_eq_mul]
      rw [mul_comm]
      congr 1
      unfold wave
      push_cast
      congr 1
      ring
    · simp [hv]
  rw [he,integral_indicator measurableSet_Ioc,← intervalIntegral.integral_of_le (Fact.out : 0 < L).le]
  simp only [intervalFourierCoefficient,one_div,Complex.ofReal_inv]

/-- Riemann–Lebesgue decay along both positive and negative integer frequencies.
No hypothesis is needed with Mathlib's convention for nonintegrable Bochner integrals. -/
theorem tendsto_intervalFourierCoefficient_cofinite (f : ℝ → ℂ) :
    Tendsto (intervalFourierCoefficient L f) cofinite (𝓝 0) := by
  have hc : Tendsto (fun n : ℤ => (n:ℝ)/L) cofinite (cocompact ℝ) := by
    convert Int.tendsto_zmultiplesHom_cofinite (inv_ne_zero (Fact.out : 0 < L).ne') using 1
    ext n
    simp [zmultiplesHom,div_eq_mul_inv,zsmul_eq_mul]
  have h := ((Real.tendsto_integral_exp_smul_cocompact ((Ioc (0:ℝ) L).indicator f)).comp hc).const_mul (L:ℂ)⁻¹
  simpa only [Function.comp_def,mul_zero,← intervalFourierCoefficient_eq_restrictedFourier] using h

/-- The same decay on the actual physical circle, with normalized Haar coefficients. -/
theorem tendsto_fourierCoeff_cofinite (f : AddCircle L → ℂ) :
    Tendsto (fourierCoeff f) cofinite (𝓝 0) := by
  have he (n : ℤ) : intervalFourierCoefficient L (fun x : ℝ => f (x : AddCircle L)) n =
      fourierCoeff f n := by
    rw [intervalFourierCoefficient_eq_fourierCoeffOn (Fact.out : 0 < L),
      fourierCoeffOn_eq_integral,fourierCoeff_eq_intervalIntegral _ _ 0]
    simp only [fourier_coe_apply,zero_add,sub_zero,smul_eq_mul,Complex.real_smul]
  rw [← funext he]
  exact tendsto_intervalFourierCoefficient_cofinite (L := L) (fun x : ℝ => f (x : AddCircle L))

namespace PeriodicFourierLebesgue
open SmoothPeriodicTest

/-- Fourier cutoffs of an interval L¹ function converge in the original FL∞ norm. -/
theorem tendsto_truncate_ofIntervalL1 (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) :
    Tendsto (fun S : Finset ℤ => truncate Weight.one ⊤ Weight.hasTemperedInverse_one S (ofIntervalL1 f hf))
      atTop (𝓝 (ofIntervalL1 f hf)) := by
  apply (tendsto_truncate_top_iff Weight.one Weight.hasTemperedInverse_one _).mpr
  intro ε hε
  have h := Metric.tendsto_nhds.mp (tendsto_intervalFourierCoefficient_cofinite (L := L) f) ε hε
  have hfin : {n : ℤ | ¬ ‖intervalFourierCoefficient L f n‖ < ε}.Finite := by
    simpa only [dist_zero_right,Filter.eventually_cofinite] using h
  refine ⟨hfin.toFinset,fun n hn => ?_⟩
  have hn' : ‖intervalFourierCoefficient L f n‖ < ε := by
    simpa only [Set.Finite.mem_toFinset,mem_ofPred_eq,not_not] using hn
  change ‖(Weight.one n : ℂ)*Distribution.ofL1 f hf (mode (-n))‖ ≤ ε
  simpa only [Weight.one_apply,Complex.ofReal_one,one_mul,Distribution.ofL1_coefficient] using hn'.le

end PeriodicFourierLebesgue
namespace SmoothPeriodicTest.Distribution

/-- Point evaluation at zero is a pseudomeasure which has no interval L¹ representative. -/
theorem evaluation_zero_not_ofL1 :
    ¬∃ (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L), ofL1 f hf = evaluation (L := L) 0 := by
  rintro ⟨f,hf,he⟩
  have hc (n : ℤ) : intervalFourierCoefficient L f n = 1 := by
    rw [← ofL1_coefficient f hf n,he,evaluation_zero_coefficient]
  have h := tendsto_intervalFourierCoefficient_cofinite (L := L) f
  simp only [show intervalFourierCoefficient L f = fun _ => (1:ℂ) from funext hc] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

end SmoothPeriodicTest.Distribution
end NLS.Fourier
