import NLS.Fourier.PeriodTwoRestrictionIntegrals
import NLS.Fourier.HalfIntervalL2Identification
import NLS.Fourier.IntervalL2Realization
import NLS.Fourier.FoldedSobolev

/-! # Actual restriction of arbitrary period-two L² data

A zero-extended unit wave represents each restriction coefficient as a
bounded Hilbert functional. Density identifies it with the completed
restriction map, and Parseval identifies its value with the physical integral.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped ComplexConjugate ENNReal
namespace NLS.Fourier

/-- A unit Fourier test wave, zero extended to the second half with the normalization two. -/
def periodTwoRestrictionTestFunction (n : ℤ) : ℝ → ℂ :=
  folded 0 (fun x => 2 * wave (2*n) x) (fun _ => 0)

theorem memLp_periodTwoRestrictionTestFunction (n : ℤ) :
    MemLp (periodTwoRestrictionTestFunction n) 2 (volume.restrict (Ioc 0 2)) :=
  memLp_two_folded 0 (continuous_const.mul (continuous_wave _)) continuous_const

def periodTwoRestrictionTest (n : ℤ) : Coeff 2 :=
  periodTwoL2Coefficients (periodTwoRestrictionTestFunction n) (memLp_periodTwoRestrictionTestFunction n)

/-- The test coefficients are conjugates of the actual unit-interval overlap. -/
theorem periodTwoRestrictionTest_apply (n k : ℤ) :
    periodTwoRestrictionTest n k = conj (intervalFourierCoefficient 1 (wave k) n) := by
  rw [periodTwoRestrictionTest, periodTwoL2Coefficients_apply, periodTwoRestrictionTestFunction,
    periodTwoCoefficient_folded 0 (fun x : ℝ => 2 * wave (2*n) x) (fun _ => 0) (by fun_prop) continuous_const k,
    zero_mul, add_zero, intervalFourierCoefficient_one_wave]
  unfold halfCoefficient unitIntegral
  rw [← intervalIntegral.intervalIntegral_conj]
  have he : (fun x : ℝ => 2 * wave (2*n) x * wave (-k) x) =
      (fun x => 2 * wave (-(k-2*n)) x) := by
    funext x
    rw [mul_assoc, ← wave_add]
    congr 2
    ring
  rw [he, intervalIntegral.integral_const_mul]
  simp only [← wave_neg]
  ring

/-- The Hilbert functional for one coefficient of the actual restriction. -/
def periodTwoRestrictionL2Functional (n : ℤ) : Coeff 2 →L[ℂ] ℂ :=
  innerSL ℂ (periodTwoRestrictionTest n)

/-- Completion by continuity gives the same restriction coefficient on all ℓ² inputs. -/
theorem periodTwoToUnit_two_apply (a : Coeff 2) (n : ℤ) :
    periodTwoToUnit (by norm_num) (by simp) a n = periodTwoRestrictionL2Functional n a := by
  let F : Coeff 2 →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
    (periodTwoToUnit (by norm_num) (by simp))
  let G := periodTwoRestrictionL2Functional n
  have hs (k : ℤ) (c : ℂ) : F (Coeff.ofFinsupp (Finsupp.single k c)) =
      G (Coeff.ofFinsupp (Finsupp.single k c)) := by
    change periodTwoToUnit (by norm_num) (by simp) (Coeff.ofFinsupp (Finsupp.single k c)) n = _
    rw [periodTwoToUnit_single_integral]
    have he : Coeff.ofFinsupp (p := 2) (Finsupp.single k c) = lp.single 2 k c := by ext j; simp [Finsupp.single_apply, lp.single_apply, Pi.single_apply, eq_comm]
    change _ = inner ℂ (periodTwoRestrictionTest n) (Coeff.ofFinsupp (Finsupp.single k c))
    rw [he, lp.inner_single_right, RCLike.inner_apply', periodTwoRestrictionTest_apply]
    simp [mul_comm]
  have hfinite (c : ℤ →₀ ℂ) : F (Coeff.ofFinsupp c) = G (Coeff.ofFinsupp c) := by
    have he : Coeff.ofFinsupp (p := 2) c =
        ∑ k ∈ c.support, Coeff.ofFinsupp (Finsupp.single k (c k)) := by
      rw [← map_sum]
      congr 1
      exact (Finsupp.sum_single c).symm
    rw [he, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun k _ => hs k (c k))
  have he := (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer F.continuous G.continuous
    (funext hfinite)
  exact congrFun he a

/-- The arbitrary L² restriction coefficient is its original physical unit Fourier integral. -/
theorem periodTwoRestrictionL2Functional_ofFunction (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) (n : ℤ) :
    periodTwoRestrictionL2Functional n (periodTwoL2Coefficients f hf) =
      intervalFourierCoefficient 1 f n := by
  have hi := lp.hasSum_inner (𝕜 := ℂ) (periodTwoRestrictionTest n) (periodTwoL2Coefficients f hf)
  have hp := hasSum_sesquilinear_intervalFourierCoefficient (by norm_num : (0 : ℝ) < 2)
    hf (memLp_periodTwoRestrictionTestFunction n)
  simp only [RCLike.inner_apply', periodTwoRestrictionTest, periodTwoL2Coefficients_apply, mul_comm] at hi
  simp only [intervalFourierCoefficient_two] at hp
  have hinner := hi.unique hp
  change inner ℂ (periodTwoRestrictionTest n) (periodTwoL2Coefficients f hf) = _
  rw [periodTwoRestrictionTest, hinner]
  have hfu : MemLp f 2 (volume.restrict (Ioc 0 1)) :=
    hf.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc le_rfl (by norm_num)) le_rfl)
  have hfi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (hfu.integrable (by norm_num))
  let g := fun x : ℝ => 2 * (f x * wave (-(2*n)) x)
  have hgi : IntervalIntegrable g volume 0 1 :=
    (hfi.mul_continuousOn (continuous_wave _).continuousOn).const_mul 2
  have he (x : ℝ) : f x * conj (periodTwoRestrictionTestFunction n x) = folded 0 g (fun _ => 0) x := by
    unfold periodTwoRestrictionTestFunction folded
    (split_ifs <;> simp [g, map_mul, map_ofNat, ← wave_neg]); ring
  simp only [he]
  have hz0 : periodTwoCoefficient (folded 0 g (fun _ => 0)) 0 =
      (2 : ℂ)⁻¹ * ∫ x in (0 : ℝ)..2, folded 0 g (fun _ => 0) x := by
    simp [periodTwoCoefficient, one_div]
  simp only [Complex.ofReal_ofNat]
  rw [← hz0]
  rw [periodTwoCoefficient_folded_of_intervalIntegrable 0 hgi (by simp), zero_mul, add_zero]
  rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num), fourierCoeffOn_one]
  simp only [halfCoefficient, g, neg_zero, wave_zero, mul_one]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Actual L² restriction, with no endpoint matching or period-one assumption. -/
theorem periodTwoToUnit_two_ofFunction (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) (n : ℤ) :
    periodTwoToUnit (by norm_num) (by simp) (periodTwoL2Coefficients f hf) n =
      intervalFourierCoefficient 1 f n := by
  rw [periodTwoToUnit_two_apply, periodTwoRestrictionL2Functional_ofFunction]

/-- Equality with the actual coefficient sequence of the restricted physical function. -/
theorem periodTwoToUnit_two_eq_unitIntervalCoefficients (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hf1 : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    periodTwoToUnit (by norm_num) (by simp) (periodTwoL2Coefficients f hf) =
      unitIntervalMemLpCoefficients f hf1 := by
  ext n
  rw [periodTwoToUnit_two_ofFunction, unitIntervalMemLpCoefficients_apply]

/-- Unit-period synthesis of the restricted coefficients recovers the input on the original interval. -/
theorem periodTwoToUnit_two_reconstruct (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hf1 : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    intervalPullback 1 (l2Synthesis
      (periodTwoToUnit (by norm_num) (by simp) (periodTwoL2Coefficients f hf)))
      =ᵐ[volume.restrict (Ioo 0 1)] f := by
  rw [periodTwoToUnit_two_eq_unitIntervalCoefficients f hf hf1]
  change intervalPullback 1 (fourierBasis.repr.symm
    (fourierBasis.repr (intervalL2Class (by norm_num) f hf1))) =ᵐ[volume.restrict (Ioo 0 1)] f
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact intervalPullback_intervalL2Class (by norm_num) f hf1

end NLS.Fourier
