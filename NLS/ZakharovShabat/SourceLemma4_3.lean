import NLS.ZakharovShabat.SourceBoundarySeries
import NLS.ZakharovShabat.BoundedIntervalExtension
import NLS.SequenceSpaces.PairComponentHolder

/-!
# Lemma 4.3 in the original source norms

For 1 < p < infinity, signed interval extension is bounded and complex analytic
from the original period-one component-sum space into the original period-two
boundary space. Its unique continuous extension retains the exact physical
finite-input Fourier formulas. At p = 2 it preserves the original norm.
The printed proof drops the half normalization at even indices and uses an
incorrect odd-kernel constant; explicit physical counterexamples are included.
-/

noncomputable section
open scoped ENNReal SchwartzMap
open NLS.Fourier
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Completed boundary amplitudes of an original-norm period-one coefficient pair. -/
def sourceIntervalAmplitudeCLM (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤) :
    CoeffPair p →L[ℂ] Coeff p :=
  (intervalAmplitudeCLM b hp1 hp).comp (CoeffPair.toMax p).toContinuousLinearMap

/-- Lemma 4.3: extension into the original-norm closed boundary space at Sobolev order zero. -/
def sourceIntervalExtensionToBoundary (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤) :
    CoeffPair p →L[ℂ] sourceWeightedBoundarySubspace (p := p) b 0 :=
  (sourceWeightedBoundaryAmplitudeEquiv b 0).toContinuousLinearMap.comp
    ((WeightedCoeff.weightIsometry (Weight.sobolev 0) p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (sourceIntervalAmplitudeCLM b hp1 hp))

/-- The original output norm retains the exact boundary-amplitude factor. -/
theorem norm_sourceIntervalExtensionToBoundary (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) : ‖sourceIntervalExtensionToBoundary b hp1 hp a‖ =
      (2 : ℝ)^(1/p.toReal) * ‖sourceIntervalAmplitudeCLM b hp1 hp a‖ := by
  change ‖sourceWeightedBoundaryAmplitudeEquiv b 0
    ((WeightedCoeff.weightIsometry (Weight.sobolev 0) p).symm (sourceIntervalAmplitudeCLM b hp1 hp a))‖ = _
  rw [norm_sourceWeightedBoundaryAmplitudeEquiv hp, LinearIsometryEquiv.norm_map]

/-- The two component factors cancel, giving the sufficient bound 2 times the half-interval bound. -/
theorem norm_sourceIntervalExtensionToBoundary_le (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) : ‖sourceIntervalExtensionToBoundary b hp1 hp a‖ ≤ intervalExtensionBound hp1 hp * ‖a‖ := by
  rw [norm_sourceIntervalExtensionToBoundary]
  have h := norm_intervalAmplitudeCLM_le b hp1 hp (CoeffPair.toMax p a)
  have hc := CoeffPair.componentNormSum_le hp a
  change ‖sourceIntervalAmplitudeCLM b hp1 hp a‖ ≤ halfIntervalBound hp1 hp * (‖a.fst‖ + ‖a.snd‖) at h
  calc
    _ ≤ (2 : ℝ)^(1/p.toReal) * (halfIntervalBound hp1 hp * (CoeffPair.l1Factor p * ‖a‖)) :=
      mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hc (halfIntervalBound_pos hp1 hp).le)) (by positivity)
    _ = _ := by
      have he := CoeffPair.l1Factor_mul_rpow p
      unfold intervalExtensionBound
      calc
        _ = (CoeffPair.l1Factor p * (2 : ℝ)^(1/p.toReal)) *
            (halfIntervalBound hp1 hp * ‖a‖) := by ring
        _ = _ := by rw [he]; ring

/-- Bounded complex linearity gives the asserted analyticity at every original input. -/
theorem analyticAt_sourceIntervalExtensionToBoundary (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) : AnalyticAt ℂ (sourceIntervalExtensionToBoundary b hp1 hp) a :=
  (sourceIntervalExtensionToBoundary b hp1 hp).analyticAt a

/-- The second raw coefficient is exactly the completed amplitude. -/
theorem sourceIntervalExtensionToBoundary_snd (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) (n : ℤ) :
    (sourceIntervalExtensionToBoundary b hp1 hp a).val.snd.val n =
      sourceIntervalAmplitudeCLM b hp1 hp a n := by
  change ((sourceWeightedBoundaryAmplitudeEquiv b 0
    ((WeightedCoeff.weightIsometry (Weight.sobolev 0) p).symm (sourceIntervalAmplitudeCLM b hp1 hp a))).val).snd.val n = _
  rw [sourceWeightedBoundaryAmplitudeEquiv_apply]
  change sourceIntervalAmplitudeCLM b hp1 hp a n / (Weight.sobolev 0 n : ℂ) = _
  simp

/-- The two-sided unit constant refutes the printed even formula without its half factor. -/
theorem sourceLemma4_3_printed_even_counterexample :
    intervalAmplitude .dirichlet (fun _ => ((1 : ℂ), 1)) 0 ≠ (1 : ℂ) + 1 := by
  rw [intervalAmplitude_dirichlet_unit_zero]
  norm_num

/-- A one-sided unit constant refutes the printed odd kernel constant. -/
theorem sourceLemma4_3_printed_odd_counterexample :
    intervalAmplitude .dirichlet (fun _ => ((0 : ℂ), 1)) 1 ≠ (-2 : ℂ) * Complex.I := by
  have he := intervalAmplitude_oneSided_odd .dirichlet 0
  norm_num only [mul_zero, zero_add, Int.cast_zero, mul_one] at he
  rw [he]
  intro h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [div_eq_iff hpi] at h
  have hi := congrArg Complex.im h
  simp at hi
  nlinarith [Real.two_le_pi]

/-- The first raw coefficient reverses the frequency and carries the boundary sign. -/
theorem sourceIntervalExtensionToBoundary_fst (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) (n : ℤ) :
    (sourceIntervalExtensionToBoundary b hp1 hp a).val.fst.val n =
      b.extensionSign * sourceIntervalAmplitudeCLM b hp1 hp a (-n) := by
  rw [(mem_sourceWeightedBoundarySubspace b 0 _).mp
    (sourceIntervalExtensionToBoundary b hp1 hp a).property n,
    sourceIntervalExtensionToBoundary_snd]

/-- Finite-input amplitudes are exactly the original physical half-interval integrals. -/
theorem sourceIntervalAmplitudeCLM_finite (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    sourceIntervalAmplitudeCLM b hp1 hp ((CoeffPair.toMax p).symm (finitePairCoeffs a)) n =
      intervalAmplitude b (periodOnePair a) n := by
  change intervalAmplitudeCLM b hp1 hp
    (CoeffPair.toMax p ((CoeffPair.toMax p).symm (finitePairCoeffs a))) n = _
  rw [ContinuousLinearEquiv.apply_symm_apply, intervalAmplitudeCLM_finite, finiteIntervalAmplitude_apply]

/-- Both output components are the actual normalized Fourier integrals of the signed reflection. -/
theorem sourceIntervalExtensionToBoundary_finite_integrals (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    let u := sourceIntervalExtensionToBoundary b hp1 hp ((CoeffPair.toMax p).symm (finitePairCoeffs a))
    (u.val.fst.val n, u.val.snd.val n) =
      (periodTwoCoefficient (fun x => (intervalExtension b (periodOnePair a) x).1) n,
        periodTwoCoefficient (fun x => (intervalExtension b (periodOnePair a) x).2) n) := by
  dsimp only
  rw [sourceIntervalExtensionToBoundary_fst, sourceIntervalExtensionToBoundary_snd,
    sourceIntervalAmplitudeCLM_finite, sourceIntervalAmplitudeCLM_finite,
    intervalExtension_coefficient_fst b _ (continuous_periodOnePair a),
    intervalExtension_coefficient_snd b _ (continuous_periodOnePair a)]

/-- The correct even formula retains the printed expansion’s factor one half. -/
theorem sourceIntervalAmplitudeCLM_even (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) (n : ℤ) :
    sourceIntervalAmplitudeCLM b hp1 hp a (2*n) = (a.snd n + b.extensionSign * a.fst (-n)) / 2 :=
  intervalAmplitudeCLM_even b hp1 hp _ n

/-- The correct odd formula uses the normalized shifted Hilbert transform. -/
theorem sourceIntervalAmplitudeCLM_odd (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) (n : ℤ) :
    sourceIntervalAmplitudeCLM b hp1 hp a (2*n+1) = (Complex.I/2 : ℂ) *
      (shiftedHilbertTransform hp1 hp a.snd n +
        b.extensionSign * shiftedHilbertTransform hp1 hp a.fst (-n-1)) :=
  intervalAmplitudeCLM_odd b hp1 hp _ n

/-- At the Hilbert exponent the original interval-extension norm is preserved exactly. -/
theorem norm_sourceIntervalExtensionToBoundary_two (b : BoundaryCondition) (a : CoeffPair 2) :
    ‖sourceIntervalExtensionToBoundary b (by norm_num) (by simp) a‖ = ‖a‖ := by
  have h := norm_hilbertIntervalExtension_sq b (CoeffPair.toMax 2 a)
  rw [← intervalExtensionCLM_two, norm_intervalExtensionCLM] at h
  change ‖sourceIntervalAmplitudeCLM b (by norm_num) (by simp) a‖ ^ 2 =
    (‖a.fst‖ ^ 2 + ‖a.snd‖ ^ 2) / 2 at h
  have ha := norm_withLp_prod_rpow (by simp : (2 : ℝ≥0∞) ≠ ⊤) a
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ha
  have ho : ‖sourceIntervalExtensionToBoundary b (by norm_num) (by simp) a‖ ^ 2 =
      2 * ‖sourceIntervalAmplitudeCLM b (by norm_num) (by simp) a‖ ^ 2 := by
    rw [norm_sourceIntervalExtensionToBoundary, ENNReal.toReal_ofNat,
      ← Real.sqrt_eq_rpow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [norm_nonneg a, norm_nonneg (sourceIntervalExtensionToBoundary b (by norm_num) (by simp) a)]

/-- Agreement with every physical finite-input extension uniquely determines the continuous map. -/
theorem sourceIntervalExtensionToBoundary_unique (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : CoeffPair p →L[ℂ] sourceWeightedBoundarySubspace (p := p) b 0)
    (hF : ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ),
      F ((CoeffPair.toMax p).symm (finitePairCoeffs a)) =
        sourceIntervalExtensionToBoundary b hp1 hp ((CoeffPair.toMax p).symm (finitePairCoeffs a))) :
    F = sourceIntervalExtensionToBoundary b hp1 hp := by
  have hd : DenseRange (fun a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ) =>
      (CoeffPair.toMax p).symm (finitePairCoeffs a)) :=
    (CoeffPair.toMax p).symm.surjective.denseRange.comp (denseRange_finitePairCoeffs hp)
      (CoeffPair.toMax p).symm.continuous
  have he : (F : CoeffPair p → sourceWeightedBoundarySubspace (p := p) b 0) =
      sourceIntervalExtensionToBoundary b hp1 hp :=
    hd.equalizer F.continuous (sourceIntervalExtensionToBoundary b hp1 hp).continuous (funext hF)
  exact ContinuousLinearMap.ext (congrFun he)

/-- Simultaneous finite Fourier truncation in the original period-one pair space. -/
def sourceIntervalInputTruncate (S : Finset ℤ) (a : CoeffPair p) : CoeffPair p :=
  (CoeffPair.toMax p).symm (Coeff.truncate S a.fst, Coeff.truncate S a.snd)

/-- The actual finite-input approximations converge in the original source norm. -/
theorem tendsto_sourceIntervalInputTruncate (hp : p ≠ ⊤) (a : CoeffPair p) :
    Filter.Tendsto (fun S : Finset ℤ => sourceIntervalInputTruncate S a) Filter.atTop (nhds a) := by
  have h := ((CoeffPair.toMax p).symm.continuous.tendsto (CoeffPair.toMax p a)).comp
    ((Coeff.tendsto_truncate hp a.fst).prodMk_nhds (Coeff.tendsto_truncate hp a.snd))
  simpa only [sourceIntervalInputTruncate, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using h

/-- The original boundary-valued extension is the norm limit of its finite-input extensions. -/
theorem tendsto_sourceIntervalExtension_truncate (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) :
    Filter.Tendsto (fun S : Finset ℤ => sourceIntervalExtensionToBoundary b hp1 hp (sourceIntervalInputTruncate S a))
      Filter.atTop (nhds (sourceIntervalExtensionToBoundary b hp1 hp a)) :=
  ((sourceIntervalExtensionToBoundary b hp1 hp).continuous.tendsto a).comp (tendsto_sourceIntervalInputTruncate hp a)

/-- The extension as a continuous linear map to actual periodic tempered-distribution pairs. -/
def sourceIntervalExtensionDistributionCLM (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤) :
    CoeffPair p →L[ℂ] 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  ((sobolevDistributionSynthesisCLM 0).prodMap (sobolevDistributionSynthesisCLM 0)).comp
    ((WeightedCoeffPair.toMax (Weight.sobolev 0) p).toContinuousLinearMap.comp
      ((sourceWeightedBoundarySubspace (p := p) b 0).subtypeL.comp (sourceIntervalExtensionToBoundary b hp1 hp)))

/-- Every rough input has an actual distributional extension obtained as the limit of finite inputs. -/
theorem tendsto_sourceIntervalExtensionDistribution_truncate (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) :
    Filter.Tendsto (fun S : Finset ℤ => sourceIntervalExtensionDistributionCLM b hp1 hp (sourceIntervalInputTruncate S a))
      Filter.atTop (nhds (sourceIntervalExtensionDistributionCLM b hp1 hp a)) :=
  ((sourceIntervalExtensionDistributionCLM b hp1 hp).continuous.tendsto a).comp
    (tendsto_sourceIntervalInputTruncate hp a)

/-- The distributional output retains every actual source Fourier coefficient. -/
theorem sourceIntervalExtensionDistribution_coefficients (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) (n : ℤ) :
    ((sourceIntervalExtensionDistributionCLM b hp1 hp a).1 (coefficientTest n),
      (sourceIntervalExtensionDistributionCLM b hp1 hp a).2 (coefficientTest n)) =
      (b.extensionSign * sourceIntervalAmplitudeCLM b hp1 hp a (-n), sourceIntervalAmplitudeCLM b hp1 hp a n) := by
  change (sobolevDistributionSynthesisCLM 0 (sourceIntervalExtensionToBoundary b hp1 hp a).val.fst (coefficientTest n),
    sobolevDistributionSynthesisCLM 0 (sourceIntervalExtensionToBoundary b hp1 hp a).val.snd (coefficientTest n)) = _
  rw [sobolevDistributionSynthesisCLM_coefficientTest, sobolevDistributionSynthesisCLM_coefficientTest,
    sourceIntervalExtensionToBoundary_fst, sourceIntervalExtensionToBoundary_snd]

/-- Convert the source’s signed finite coefficients to raw scalar Fourier coordinates. -/
def sourceSignedFinitePair (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) : (ℤ →₀ ℂ) × (ℤ →₀ ℂ) :=
  (Finsupp.mapDomain (fun n : ℤ => -n) a.1, a.2)

/-- The first signed coefficient has the opposite scalar Fourier index. -/
theorem sourceSignedFinitePair_fst (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    (sourceSignedFinitePair a).1 n = a.1 (-n) := by
  change Finsupp.mapDomain (fun n : ℤ => -n) a.1 n = _
  simpa only [Equiv.neg_apply, neg_neg] using Finsupp.mapDomain_apply (Equiv.neg ℤ).injective a.1 (-n)

/-- The corrected even formula in the literal signed source coefficient convention. -/
theorem sourceLemma4_3_even_signed (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    intervalAmplitude b (periodOnePair (sourceSignedFinitePair a)) (2*n) =
      (1/2 : ℂ) * (a.2 n + b.extensionSign * a.1 n) := by
  rw [intervalAmplitude_even, sourceSignedFinitePair_fst, neg_neg]
  rfl

/-- The corrected odd kernel in the literal signed source convention, with factor i/pi. -/
theorem sourceLemma4_3_odd_signed (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    intervalAmplitude b (periodOnePair (sourceSignedFinitePair a)) (2*n+1) =
      a.2.sum (fun k z => z * (Complex.I / ((Real.pi : ℂ) * (2*k-2*n-1)))) -
      b.extensionSign * a.1.sum (fun k z => z * (Complex.I / ((Real.pi : ℂ) * (2*k-2*n-1)))) := by
  rw [intervalAmplitude_odd]
  change a.2.sum _ + b.extensionSign * (Finsupp.mapDomain (fun k : ℤ => -k) a.1).sum _ = _
  rw [Finsupp.sum_mapDomain_index (by intro k; simp) (by intro k x y; ring)]
  simp only [Int.cast_neg]
  have he : a.1.sum (fun k z => z * (Complex.I / ((Real.pi : ℂ) * (2 * -(k : ℂ) + 2*n + 1)))) =
      -a.1.sum (fun k z => z * (Complex.I / ((Real.pi : ℂ) * (2*k-2*n-1)))) := by
    unfold Finsupp.sum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only
    have hd : (Real.pi : ℂ) * (2 * -(k : ℂ) + 2*n + 1) = -((Real.pi : ℂ) * (2*k-2*n-1)) := by ring
    rw [hd, div_neg, mul_neg]
  rw [he]
  ring

/-- The completed distributional extension has period two in each component. -/
theorem sourceIntervalExtensionDistribution_periodic (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) :
    IsPeriodTwoDistribution (sourceIntervalExtensionDistributionCLM b hp1 hp a).1 ∧
      IsPeriodTwoDistribution (sourceIntervalExtensionDistributionCLM b hp1 hp a).2 :=
  ⟨isPeriodTwoDistribution_weightedDistributionSynthesis _ _ _,
    isPeriodTwoDistribution_weightedDistributionSynthesis _ _ _⟩

/-- Lemma 4.3: one positive bound works for both original-norm boundary maps, and both are analytic. -/
theorem sourceLemma4_3 (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : BoundaryCondition,
      (∀ a : CoeffPair p, ‖sourceIntervalExtensionToBoundary b hp1 hp a‖ ≤ C * ‖a‖) ∧
      (∀ a : CoeffPair p, AnalyticAt ℂ (sourceIntervalExtensionToBoundary b hp1 hp) a) :=
  ⟨intervalExtensionBound hp1 hp, intervalExtensionBound_pos hp1 hp, fun b =>
    ⟨norm_sourceIntervalExtensionToBoundary_le b hp1 hp,
      analyticAt_sourceIntervalExtensionToBoundary b hp1 hp⟩⟩

end NLS.ZakharovShabat
