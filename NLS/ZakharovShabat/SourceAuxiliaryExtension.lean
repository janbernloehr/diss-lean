import NLS.ZakharovShabat.SourceAuxiliarySpaces
import NLS.ZakharovShabat.SourceLemma4_4
import NLS.ZakharovShabat.AuxiliarySourceExtension
/-!
# Completed auxiliary extensions in the original norms

The page-34 extension maps into the actual zero-order auxiliary subspace.
Its sufficient bound is the ordinary interval-extension bound, since the
auxiliary phase preserves the original input norm. Physical finite Fourier
formulas, completion by density, and actual distributional limits identify
the map. At p=2 the original component-sum norm is preserved exactly.
-/

noncomputable section
open scoped ENNReal SchwartzMap
open NLS.Fourier
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Auxiliary phase on the original finite-exponent input norm. -/
def sourceAuxiliaryInputPhase (hp : p ≠ ⊤) : CoeffPair p ≃ₗᵢ[ℂ] CoeffPair p where
  toFun u := WithLp.toLp p (u.ofLp.1, Complex.I • u.ofLp.2)
  invFun u := WithLp.toLp p (u.ofLp.1, -Complex.I • u.ofLp.2)
  left_inv u := by apply WithLp.ofLp_injective; simp [smul_smul]; rfl
  right_inv u := by apply WithLp.ofLp_injective; simp [smul_smul]; rfl
  map_add' u v := by apply WithLp.ofLp_injective; simp [smul_add]
  map_smul' c u := by
    apply WithLp.ofLp_injective
    exact Prod.ext rfl (smul_comm Complex.I c u.ofLp.2)
  norm_map' u := by
    have hp0 : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
    simp [WithLp.prod_norm_eq_add hp0, norm_smul]

/-- Completed scalar amplitudes of the auxiliary reflection in the original input norm. -/
def sourceAuxiliaryIntervalAmplitudeCLM (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤) :
    CoeffPair p →L[ℂ] Coeff p :=
  (sourceIntervalAmplitudeCLM b hp1 hp).comp (sourceAuxiliaryInputPhase hp).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The page-34 map into the actual original auxiliary space at Sobolev order zero. -/
def sourceAuxiliaryExtensionToBoundary (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤) :
    CoeffPair p →L[ℂ] sourceWeightedAuxiliarySubspace (p := p) b 0 :=
  (sourceWeightedAuxiliaryAmplitudeEquiv b 0).toContinuousLinearMap.comp
    ((WeightedCoeff.weightIsometry (Weight.sobolev 0) p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (sourceAuxiliaryIntervalAmplitudeCLM b hp1 hp))

theorem norm_sourceAuxiliaryExtensionToBoundary (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) : ‖sourceAuxiliaryExtensionToBoundary b hp1 hp a‖ =
      (2 : ℝ)^(1/p.toReal) * ‖sourceAuxiliaryIntervalAmplitudeCLM b hp1 hp a‖ := by
  change ‖sourceWeightedAuxiliaryAmplitudeEquiv b 0
    ((WeightedCoeff.weightIsometry (Weight.sobolev 0) p).symm (sourceAuxiliaryIntervalAmplitudeCLM b hp1 hp a))‖ = _
  rw [norm_sourceWeightedAuxiliaryAmplitudeEquiv hp, LinearIsometryEquiv.norm_map]

/-- Auxiliary phases preserve the ordinary extension bound in the original norm. -/
theorem norm_sourceAuxiliaryExtensionToBoundary_le (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) : ‖sourceAuxiliaryExtensionToBoundary b hp1 hp a‖ ≤ intervalExtensionBound hp1 hp * ‖a‖ := by
  rw [norm_sourceAuxiliaryExtensionToBoundary]
  change (2 : ℝ)^(1/p.toReal) * ‖sourceIntervalAmplitudeCLM b hp1 hp ((sourceAuxiliaryInputPhase hp).symm a)‖ ≤ _
  rw [← norm_sourceIntervalExtensionToBoundary]
  simpa only [LinearIsometryEquiv.norm_map] using
    norm_sourceIntervalExtensionToBoundary_le b hp1 hp ((sourceAuxiliaryInputPhase hp).symm a)

theorem analyticAt_sourceAuxiliaryExtensionToBoundary (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) : AnalyticAt ℂ (sourceAuxiliaryExtensionToBoundary b hp1 hp) a :=
  (sourceAuxiliaryExtensionToBoundary b hp1 hp).analyticAt a

/-- The positive raw coefficient has exactly the auxiliary phase. -/
theorem sourceAuxiliaryExtensionToBoundary_snd (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) (n : ℤ) :
    (sourceAuxiliaryExtensionToBoundary b hp1 hp a).val.snd.val n =
      Complex.I * sourceAuxiliaryIntervalAmplitudeCLM b hp1 hp a n := by
  change ((sourceWeightedAuxiliaryAmplitudeEquiv b 0
    ((WeightedCoeff.weightIsometry (Weight.sobolev 0) p).symm (sourceAuxiliaryIntervalAmplitudeCLM b hp1 hp a))).val).snd.val n = _
  rw [sourceWeightedAuxiliaryAmplitudeEquiv_apply]
  change Complex.I * (sourceAuxiliaryIntervalAmplitudeCLM b hp1 hp a n / (Weight.sobolev 0 n : ℂ)) = _
  simp

/-- The negative raw coefficient has the boundary sign and reversed frequency. -/
theorem sourceAuxiliaryExtensionToBoundary_fst (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) (n : ℤ) :
    (sourceAuxiliaryExtensionToBoundary b hp1 hp a).val.fst.val n =
      extensionSign b * sourceAuxiliaryIntervalAmplitudeCLM b hp1 hp a (-n) := by
  rw [(mem_sourceWeightedAuxiliarySubspace b 0 _).mp
    (sourceAuxiliaryExtensionToBoundary b hp1 hp a).property n, sourceAuxiliaryExtensionToBoundary_snd]
  ring_nf
  simp

/-- Removing the zero weight gives precisely the existing completed auxiliary operator. -/
theorem sourceAuxiliaryExtensionToBoundary_eq_completed (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) :
    sourceBoundaryZeroWeightEquiv (sourceAuxiliaryExtensionToBoundary b hp1 hp a).val =
      auxiliarySourceExtension b hp1 hp a := by
  apply (CoeffPair.toMax p).injective
  rw [toMax_auxiliarySourceExtension, auxiliaryIntervalExtensionCLM_apply]
  apply Prod.ext <;> apply lp.ext <;> funext n
  · change (sourceBoundaryZeroWeightEquiv _).fst n = _
    rw [sourceBoundaryZeroWeightEquiv_fst, sourceAuxiliaryExtensionToBoundary_fst]
    rfl
  · change (sourceBoundaryZeroWeightEquiv _).snd n = _
    rw [sourceBoundaryZeroWeightEquiv_snd, sourceAuxiliaryExtensionToBoundary_snd]
    rfl

/-- The original unweighted completed map inherits the same sufficient bound. -/
theorem norm_auxiliarySourceExtension_improved_le (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) : ‖auxiliarySourceExtension b hp1 hp a‖ ≤ intervalExtensionBound hp1 hp * ‖a‖ := by
  rw [← sourceAuxiliaryExtensionToBoundary_eq_completed, sourceBoundaryZeroWeightEquiv.norm_map]
  exact norm_sourceAuxiliaryExtensionToBoundary_le b hp1 hp a

/-- The new original auxiliary target map preserves the Hilbert norm exactly. -/
theorem norm_sourceAuxiliaryExtensionToBoundary_two (b : BoundaryCondition) (a : CoeffPair 2) :
    ‖sourceAuxiliaryExtensionToBoundary b (by norm_num) (by simp) a‖ = ‖a‖ := by
  have h := norm_auxiliarySourceExtension_two b a
  rw [← sourceAuxiliaryExtensionToBoundary_eq_completed, sourceBoundaryZeroWeightEquiv.norm_map] at h
  exact h

/-- The original weighted target retains the actual physical finite-input Fourier integrals. -/
theorem sourceAuxiliaryExtensionToBoundary_finite_integrals (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    let u := sourceAuxiliaryExtensionToBoundary b hp1 hp ((CoeffPair.toMax p).symm (finitePairCoeffs a))
    (u.val.fst.val n, u.val.snd.val n) =
      (periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b (BoundaryCondition.periodOnePair a) x).1) n,
        periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b (BoundaryCondition.periodOnePair a) x).2) n) := by
  have h := auxiliarySourceExtension_finite_integrals b hp1 hp a n
  dsimp only at h ⊢
  rw [← sourceAuxiliaryExtensionToBoundary_eq_completed, sourceBoundaryZeroWeightEquiv_fst,
    sourceBoundaryZeroWeightEquiv_snd] at h
  exact h

/-- Physical finite-input agreement determines the completed auxiliary map uniquely. -/
theorem sourceAuxiliaryExtensionToBoundary_unique (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : CoeffPair p →L[ℂ] sourceWeightedAuxiliarySubspace (p := p) b 0)
    (hF : ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ),
      F ((CoeffPair.toMax p).symm (finitePairCoeffs a)) =
        sourceAuxiliaryExtensionToBoundary b hp1 hp ((CoeffPair.toMax p).symm (finitePairCoeffs a))) :
    F = sourceAuxiliaryExtensionToBoundary b hp1 hp := by
  have hd : DenseRange (fun a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ) =>
      (CoeffPair.toMax p).symm (finitePairCoeffs a)) :=
    (CoeffPair.toMax p).symm.surjective.denseRange.comp (denseRange_finitePairCoeffs hp)
      (CoeffPair.toMax p).symm.continuous
  have he : (F : CoeffPair p → sourceWeightedAuxiliarySubspace (p := p) b 0) =
      sourceAuxiliaryExtensionToBoundary b hp1 hp :=
    hd.equalizer F.continuous (sourceAuxiliaryExtensionToBoundary b hp1 hp).continuous (funext hF)
  exact ContinuousLinearMap.ext (congrFun he)

/-- Rough auxiliary extensions are original-norm limits of finite Fourier inputs. -/
theorem tendsto_sourceAuxiliaryExtension_truncate (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) :
    Filter.Tendsto (fun S : Finset ℤ => sourceAuxiliaryExtensionToBoundary b hp1 hp (sourceIntervalInputTruncate S a))
      Filter.atTop (nhds (sourceAuxiliaryExtensionToBoundary b hp1 hp a)) :=
  ((sourceAuxiliaryExtensionToBoundary b hp1 hp).continuous.tendsto a).comp (tendsto_sourceIntervalInputTruncate hp a)

/-- The completed auxiliary reflection as an actual periodic distributional pair. -/
def sourceAuxiliaryExtensionDistributionCLM (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤) :
    CoeffPair p →L[ℂ] 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  ((sobolevDistributionSynthesisCLM 0).prodMap (sobolevDistributionSynthesisCLM 0)).comp
    ((WeightedCoeffPair.toMax (Weight.sobolev 0) p).toContinuousLinearMap.comp
      ((sourceWeightedAuxiliarySubspace (p := p) b 0).subtypeL.comp (sourceAuxiliaryExtensionToBoundary b hp1 hp)))

theorem tendsto_sourceAuxiliaryExtensionDistribution_truncate (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) :
    Filter.Tendsto (fun S : Finset ℤ => sourceAuxiliaryExtensionDistributionCLM b hp1 hp (sourceIntervalInputTruncate S a))
      Filter.atTop (nhds (sourceAuxiliaryExtensionDistributionCLM b hp1 hp a)) :=
  ((sourceAuxiliaryExtensionDistributionCLM b hp1 hp).continuous.tendsto a).comp
    (tendsto_sourceIntervalInputTruncate hp a)

/-- The distributional extension retains the exact source coefficients and phases. -/
theorem sourceAuxiliaryExtensionDistribution_coefficients (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : CoeffPair p) (n : ℤ) :
    ((sourceAuxiliaryExtensionDistributionCLM b hp1 hp a).1 (coefficientTest n),
      (sourceAuxiliaryExtensionDistributionCLM b hp1 hp a).2 (coefficientTest n)) =
      (b.extensionSign * sourceAuxiliaryIntervalAmplitudeCLM b hp1 hp a (-n), Complex.I * sourceAuxiliaryIntervalAmplitudeCLM b hp1 hp a n) := by
  change (sobolevDistributionSynthesisCLM 0 (sourceAuxiliaryExtensionToBoundary b hp1 hp a).val.fst (coefficientTest n),
    sobolevDistributionSynthesisCLM 0 (sourceAuxiliaryExtensionToBoundary b hp1 hp a).val.snd (coefficientTest n)) = _
  rw [sobolevDistributionSynthesisCLM_coefficientTest, sobolevDistributionSynthesisCLM_coefficientTest,
    sourceAuxiliaryExtensionToBoundary_fst, sourceAuxiliaryExtensionToBoundary_snd]

end NLS.ZakharovShabat
