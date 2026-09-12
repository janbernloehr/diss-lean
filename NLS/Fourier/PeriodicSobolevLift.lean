import NLS.Fourier.FoldedSobolev

/-!
# Lifting a classical Sobolev interval to the circle

Matching endpoints let an absolutely continuous function on `[0,2]` descend to
a continuous circle function. Square integrability of its actual derivative is
preserved, so the lift has weighted Fourier coordinates.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.Fourier

/-- A continuous period-two lift of an absolutely continuous function with matching endpoints. -/
def periodicSobolevLift (f : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 2)
    (hend : f 0 = f 2) : C(AddCircle (2 : ℝ), ℂ) :=
  ⟨AddCircle.liftIco 2 0 f, AddCircle.liftIco_zero_continuous hend (by simpa using hf.continuousOn)⟩

/-- Lifting retains every value of the closed physical period. -/
theorem periodicSobolevLift_apply (f : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 2)
    (hend : f 0 = f 2) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    periodicSobolevLift f hf hend (x : AddCircle (2 : ℝ)) = f x := by
  change AddCircle.liftIco 2 0 f (x : AddCircle (2 : ℝ)) = f x
  by_cases hx2 : x < 2
  · exact AddCircle.liftIco_zero_coe_apply ⟨hx.1, hx2⟩
  · have he : x = 2 := le_antisymm hx.2 (le_of_not_gt hx2)
    subst x
    have hq : ((2 : ℝ) : AddCircle (2 : ℝ)) = ((0 : ℝ) : AddCircle (2 : ℝ)) := by
      simpa only [zero_add] using AddCircle.coe_add_period (2 : ℝ) 0
    rw [hq, AddCircle.liftIco_zero_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 2)]
    exact hend

/-- The lift has the same classical derivative almost everywhere on the physical period. -/
theorem deriv_periodicSobolevLift_ae (f : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 2)
    (hend : f 0 = f 2) :
    deriv (fun x : ℝ => periodicSobolevLift f hf hend (x : AddCircle (2 : ℝ)))
      =ᵐ[volume.restrict (Ioc 0 2)] deriv f := by
  change ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 2),
    deriv (fun t : ℝ => periodicSobolevLift f hf hend (t : AddCircle (2 : ℝ))) x = deriv f x
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [(show ∀ᵐ x : ℝ, x ≠ (2 : ℝ) from by simp [ae_iff, measure_singleton])] with x hx2
  intro hx
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds hx.1 (lt_of_le_of_ne hx.2 hx2)] with y hy
  exact periodicSobolevLift_apply f hf hend ⟨hy.1.le, hy.2.le⟩

/-- Classical Sobolev regularity is preserved by the matching-endpoint lift. -/
theorem hasPeriodicH1Regularity_periodicSobolevLift (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 2)
    (hfi : MemLp (deriv f) 2 (volume.restrict (Ioc 0 2))) (hend : f 0 = f 2) :
    HasPeriodicH1Regularity (periodicSobolevLift f hf hend) := by
  constructor
  · apply FunctionalAnalysis.absolutelyContinuousOnInterval_congr hf
    intro x hx
    exact (periodicSobolevLift_apply f hf hend (by simpa using hx)).symm
  · exact (memLp_congr_ae (deriv_periodicSobolevLift_ae f hf hend)).mpr hfi

/-- The lift uses the original normalized physical Fourier integrals. -/
theorem fourierCoeff_periodicSobolevLift (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 2) (hend : f 0 = f 2) (n : ℤ) :
    fourierCoeff (periodicSobolevLift f hf hend) n = periodTwoCoefficient f n := by
  rw [← periodTwoCoefficient_circle]
  unfold periodTwoCoefficient
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [periodicSobolevLift_apply f hf hend (by simpa using hx)]

/-- The lifted function has weighted Fourier coordinates recovering the closed interval. -/
theorem exists_weighted_representation_of_interval (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 2)
    (hfi : MemLp (deriv f) 2 (volume.restrict (Ioc 0 2))) (hend : f 0 = f 2) :
    ∃ a : ZakharovShabat.ScalarDomain 2,
      (∀ n, a.val n = periodTwoCoefficient f n) ∧
      ∀ x ∈ Icc (0 : ℝ) 2, sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ)) = f x := by
  let h := hasPeriodicH1Regularity_periodicSobolevLift f hf hfi hend
  refine ⟨sobolevCoefficients (periodicSobolevLift f hf hend) h, ?_, ?_⟩
  · intro n
    rw [sobolevCoefficients_apply, fourierCoeff_periodicSobolevLift]
  · intro x hx
    rw [sobolevSynthesis_sobolevCoefficients]
    exact periodicSobolevLift_apply f hf hend hx

private theorem folded_matching_endpoints (ε : ℂ) {f g : ℝ → ℂ} (h0 : f 0 = ε * g 0) :
    folded ε f g 0 = folded ε f g 2 := by
  simpa [folded] using h0

/-- Weighted Fourier coordinates of a reflected classical interval function. -/
def foldedSobolevCoefficients (ε : ℂ) (f g : ℝ → ℂ)
    (hf : HasIntervalH1Regularity f) (hg : HasIntervalH1Regularity g)
    (h0 : f 0 = ε * g 0) (h1 : f 1 = ε * g 1) : ZakharovShabat.ScalarDomain 2 :=
  sobolevCoefficients
    (periodicSobolevLift (folded ε f g) (absolutelyContinuous_folded ε hf hg h1)
      (folded_matching_endpoints ε h0))
    (hasPeriodicH1Regularity_periodicSobolevLift _ (absolutelyContinuous_folded ε hf hg h1)
      (memLp_deriv_folded ε hf hg h1) (folded_matching_endpoints ε h0))

@[simp] theorem foldedSobolevCoefficients_apply (ε : ℂ) (f g : ℝ → ℂ)
    (hf : HasIntervalH1Regularity f) (hg : HasIntervalH1Regularity g)
    (h0 : f 0 = ε * g 0) (h1 : f 1 = ε * g 1) (n : ℤ) :
    (foldedSobolevCoefficients ε f g hf hg h0 h1).val n = periodTwoCoefficient (folded ε f g) n := by
  unfold foldedSobolevCoefficients
  rw [sobolevCoefficients_apply, fourierCoeff_periodicSobolevLift]

/-- Synthesis recovers the folded function everywhere on its closed physical period. -/
theorem sobolevSynthesis_foldedSobolevCoefficients (ε : ℂ) (f g : ℝ → ℂ)
    (hf : HasIntervalH1Regularity f) (hg : HasIntervalH1Regularity g)
    (h0 : f 0 = ε * g 0) (h1 : f 1 = ε * g 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    sobolevSynthesis (by simp) (foldedSobolevCoefficients ε f g hf hg h0 h1)
      (x : AddCircle (2 : ℝ)) = folded ε f g x := by
  unfold foldedSobolevCoefficients
  rw [sobolevSynthesis_sobolevCoefficients]
  exact periodicSobolevLift_apply _ _ _ hx

end NLS.Fourier
