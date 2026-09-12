import NLS.Fourier.CirclePrimitive
import NLS.FunctionalAnalysis.IntegralAbsoluteContinuity

/-!
# The physical derivative of a Fourier Sobolev representative

At exponent two, the Fourier derivative has an actual square-integrable
realization. Its integral on `[0,x]` is the increment of the continuous
representative, and it is the classical derivative almost everywhere in `(0,2)`.
The integral identity is obtained by continuous extension from finite modes.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier
open ZakharovShabat

/-- The square-integrable realization of the Fourier derivative. -/
def sobolevDerivative : ScalarDomain 2 →L[ℂ] CircleL2 :=
  l2Synthesis.toContinuousLinearEquiv.toContinuousLinearMap.comp derivative

@[simp] theorem fourierCoeff_sobolevDerivative (a : ScalarDomain 2) (n : ℤ) :
    fourierCoeff (sobolevDerivative a) n = Complex.I * (Real.pi : ℂ) * n * a.val n := by
  change fourierCoeff (l2Synthesis (derivative a)) n = _
  rw [fourierCoeff_l2Synthesis, derivative_apply]

theorem norm_sobolevDerivative_le (a : ScalarDomain 2) :
    ‖sobolevDerivative a‖ ≤ Real.pi * ‖a‖ :=
  (norm_l2Synthesis _).trans_le (norm_derivative_le a)

/-- The derivative is square integrable with respect to physical Lebesgue measure. -/
theorem memLp_sobolevDerivative (a : ScalarDomain 2) :
    MemLp (circlePullback (sobolevDerivative a)) 2 (volume.restrict (Ioc 0 2)) :=
  memLp_circlePullback _

/-- Classical differentiation of the physical wave, with the period-two factor. -/
theorem hasDerivAt_wave (n : ℤ) (x : ℝ) :
    HasDerivAt (wave n) (Complex.I * (Real.pi : ℂ) * n * wave n x) x := by
  have h := hasDerivAt_fourier (2 : ℝ) n x
  simp only [fourier_two_eq_wave, Complex.ofReal_ofNat] at h
  convert h using 1
  ring

private theorem derivative_scalarMode (n : ℤ) (c : ℂ) :
    derivative (scalarMode (p := 2) n c) =
      scalarInclusion (scalarMode n (Complex.I * (Real.pi : ℂ) * n * c)) := by
  ext k
  simp only [derivative_apply, scalarInclusion_apply, scalarMode_apply]
  split_ifs with h
  · subst k; rfl
  · simp

/-- Integrating the Fourier derivative gives the increment on each individual mode. -/
theorem circlePrimitive_sobolevDerivative_scalarMode {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2)
    (n : ℤ) (c : ℂ) :
    circlePrimitive x (sobolevDerivative (scalarMode n c)) =
      sobolevTrace (by simp) x (scalarMode (p := 2) n c) -
        sobolevTrace (by simp) 0 (scalarMode (p := 2) n c) := by
  change circlePrimitive x (l2Synthesis (derivative (scalarMode n c))) = _
  rw [derivative_scalarMode, ← toLp_sobolevSynthesis, circlePrimitive_toLp hx]
  simp only [sobolevTrace_apply, sobolevSynthesis_scalarMode]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    convert (hasDerivAt_wave n t).const_mul c using 1
    · rfl
    · ring
  · exact (continuous_const.mul (continuous_wave n)).intervalIntegrable 0 x

private theorem truncate_eq_sum_scalarMode (s : Finset ℤ) (a : ScalarDomain 2) :
    WeightedCoeff.truncate (Weight.sobolev 1) 2 s a = ∑ n ∈ s, scalarMode n (a.val n) := by
  classical
  apply scalarInclusion_injective
  simp only [map_sum, scalarInclusion_scalarMode]
  ext k
  rw [scalarInclusion_apply, WeightedCoeff.truncate_apply]
  change (if k ∈ s then a.val k else 0) =
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k) (∑ n ∈ s, lp.single 2 n (a.val n))
  rw [map_sum]
  change (if k ∈ s then a.val k else 0) = ∑ n ∈ s, (lp.single 2 n (a.val n)) k
  simp only [lp.single_apply, Pi.single_apply]
  simp


/-- The fundamental theorem of calculus for every weighted `ℓ2` input. -/
theorem circlePrimitive_sobolevDerivative {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2)
    (a : ScalarDomain 2) :
    circlePrimitive x (sobolevDerivative a) =
      sobolevTrace (by simp) x a - sobolevTrace (by simp) 0 a := by
  let F : ScalarDomain 2 →L[ℂ] ℂ := (circlePrimitiveCLM x hx).comp sobolevDerivative
  let G : ScalarDomain 2 →L[ℂ] ℂ := sobolevTrace (by simp) x - sobolevTrace (by simp) 0
  change F a = G a
  apply (isClosed_eq F.continuous G.continuous).mem_of_tendsto
    (WeightedCoeff.tendsto_truncate (Weight.sobolev 1) 2 (by simp) a)
  apply Filter.Eventually.of_forall
  intro s
  change F (WeightedCoeff.truncate (Weight.sobolev 1) 2 s a) =
    G (WeightedCoeff.truncate (Weight.sobolev 1) 2 s a)
  rw [truncate_eq_sum_scalarMode, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact circlePrimitive_sobolevDerivative_scalarMode hx n (a.val n)

/-- Integral reconstruction on the closed physical period. -/
theorem sobolevSynthesis_eq_trace_add_integral (a : ScalarDomain 2)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ)) =
      sobolevTrace (by simp) 0 a + ∫ t in (0 : ℝ)..x, circlePullback (sobolevDerivative a) t := by
  have h := circlePrimitive_sobolevDerivative hx a
  change _ = _ + circlePrimitive x (sobolevDerivative a)
  rw [h, add_sub_cancel]
  rfl

/-- The Fourier derivative is the classical derivative almost everywhere in the physical period. -/
theorem ae_hasDerivAt_sobolevSynthesis (a : ScalarDomain 2) :
    ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 2 →
      HasDerivAt (fun t : ℝ => sobolevSynthesis (by simp) a (t : AddCircle (2 : ℝ)))
        (circlePullback (sobolevDerivative a) x) x := by
  filter_upwards [(intervalIntegrable_circlePullback (sobolevDerivative a)).ae_hasDerivAt_integral]
    with x hx
  intro hxi
  have h := (hx (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using (⟨hxi.1.le, hxi.2.le⟩ : x ∈ Icc (0 : ℝ) 2))
    0 (by simp)).const_add (sobolevTrace (by simp) 0 a)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
  exact sobolevSynthesis_eq_trace_add_integral a ⟨hy.1.le, hy.2.le⟩

/-- The physical representative is absolutely continuous on the closed full period. -/
theorem absolutelyContinuous_sobolevSynthesis (a : ScalarDomain 2) :
    AbsolutelyContinuousOnInterval
      (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) 0 2 := by
  have hi := FunctionalAnalysis.absolutelyContinuousOnInterval_integral
    (intervalIntegrable_circlePullback (sobolevDerivative a)) (c := 0) (by simp)
  have hc := FunctionalAnalysis.absolutelyContinuousOnInterval_const_add hi
    (sobolevTrace (by simp) 0 a)
  apply FunctionalAnalysis.absolutelyContinuousOnInterval_congr hc
  intro x hx
  exact (sobolevSynthesis_eq_trace_add_integral a
    (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hx)).symm

/-- The pointwise derivative agrees almost everywhere with the Fourier `L²` derivative. -/
theorem deriv_sobolevSynthesis_ae (a : ScalarDomain 2) :
    deriv (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ)))
      =ᵐ[volume.restrict (Ioc 0 2)] circlePullback (sobolevDerivative a) := by
  change ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 2),
    deriv (fun t : ℝ => sobolevSynthesis (by simp) a (t : AddCircle (2 : ℝ))) x =
      circlePullback (sobolevDerivative a) x
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [ae_hasDerivAt_sobolevSynthesis a, (show ∀ᵐ x : ℝ, x ≠ (2 : ℝ) from by simp [ae_iff, measure_singleton])] with x hx hx2
  intro hxi
  exact (hx ⟨hxi.1, lt_of_le_of_ne hxi.2 hx2⟩).deriv

/-- The actual classical derivative is square integrable. -/
theorem memLp_deriv_sobolevSynthesis (a : ScalarDomain 2) :
    MemLp (deriv (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))))
      2 (volume.restrict (Ioc 0 2)) :=
  (memLp_congr_ae (deriv_sobolevSynthesis_ae a)).mpr (memLp_sobolevDerivative a)

/-- The actual classical derivative has exactly the Fourier multiplier `i π n`. -/
theorem periodTwoCoefficient_deriv_sobolevSynthesis (a : ScalarDomain 2) (n : ℤ) :
    periodTwoCoefficient
      (deriv (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ)))) n =
      Complex.I * (Real.pi : ℂ) * n * a.val n := by
  rw [← fourierCoeff_sobolevDerivative, ← periodTwoCoefficient_circlePullback]
  unfold periodTwoCoefficient
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  apply integral_congr_ae
  filter_upwards [deriv_sobolevSynthesis_ae a] with x hx
  exact congrArg (fun z : ℂ => z * wave (-n) x) hx

end NLS.Fourier
