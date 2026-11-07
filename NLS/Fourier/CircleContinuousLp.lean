import NLS.Fourier.SobolevSynthesis

/-! The probability Haar measure on the period-two circle is exactly the
source normalization (1/2) integral_0^2. Continuous functions enter every
Lp, including L-infinity, with norm at most their uniform norm. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- The same continuous period-two function in every normalized Lp. -/
def circleContinuousToLp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    C(AddCircle (2:ℝ),ℂ) →L[ℂ] Lp ℂ p (AddCircle.haarAddCircle (T := (2:ℝ))) :=
  ContinuousMap.toLp p AddCircle.haarAddCircle ℂ

/-- Its Lp representative is the identical continuous circle function. -/
theorem circleContinuousToLp_representative (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : C(AddCircle (2:ℝ),ℂ)) :
    circleContinuousToLp p f =ᵐ[AddCircle.haarAddCircle] f :=
  ContinuousMap.coeFn_toLp (p := p) AddCircle.haarAddCircle (𝕜 := ℂ) f

/-- The probability normalization gives the exact comparison constant one. -/
theorem norm_circleContinuousToLp_le (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : C(AddCircle (2:ℝ),ℂ)) : ‖circleContinuousToLp p f‖ ≤ ‖f‖ := by
  have hm : measureUnivNNReal (AddCircle.haarAddCircle (T := (2:ℝ))) = 1 := by
    simp [measureUnivNNReal]
  have hb := BoundedContinuousFunction.Lp_norm_le (p := p)
    (μ := AddCircle.haarAddCircle) (ContinuousMap.linearIsometryBoundedOfCompact (AddCircle (2:ℝ)) ℂ ℂ f)
  change ‖circleContinuousToLp p f‖ ≤ _ at hb
  simpa only [hm,NNReal.coe_one,Real.one_rpow,one_mul,
    LinearIsometryEquiv.norm_map] using hb

end NLS.Fourier
