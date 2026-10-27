import NLS.ZakharovShabat.SourcePeriodOneSignedSeries
import NLS.ZakharovShabat.SourceLemma4_4

/-! # Lemma 4.3 on the original periodic distributions

The completed signed reflection acts between the native period-one and
period-two smooth-test distribution spaces, in their exact finite-p source
norms. The target is the actual closed boundary subspace. The map is bounded
and analytic for 1<p<infinity, agrees with the physical normalized integrals
on signed modes, and is uniquely determined by them. Its full signed-mode
series converges in the target norm; its native and tempered realizations
agree. Both corrected even and odd coefficient formulas hold on arbitrary
rough inputs. No endpoint reflection map is asserted.
-/

noncomputable section
open scoped ENNReal SchwartzMap
open NLS NLS.Fourier NLS.Fourier.SmoothPeriodicTest
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The boundary space consists of actual period-two distributions. -/
def sourceNativeBoundarySubmodule (b : BoundaryCondition) :
    Submodule ℂ (SourcePeriodicPair 2 p) :=
  (sourceBoundaryBaseSubspace b).comap (sourcePeriodicPairCoefficients 2).toLinearMap

theorem mem_sourceNativeBoundarySubmodule (b : BoundaryCondition) (u : SourcePeriodicPair 2 p) :
    u ∈ sourceNativeBoundarySubmodule b ↔
      ∀ n : ℤ, u.fst.val (mode (-n)) = b.extensionSign * u.snd.val (mode n) := by
  change sourcePeriodicPairCoefficients 2 u ∈ sourceBoundaryBaseSubspace b ↔ _
  simp only [mem_sourceBoundaryBaseSubspace, sourcePeriodicPairCoefficients_fst,
    sourcePeriodicPairCoefficients_snd, neg_neg]

/-- The completed reflection on the original native distribution pairs. -/
def sourceNativeIntervalExtensionAmbient (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤) :
    SourcePeriodicPair 1 p →L[ℂ] SourcePeriodicPair 2 p :=
  (sourcePeriodicPairCoefficients 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sourceBoundaryZeroWeightEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((sourceWeightedBoundarySubspace b 0).subtypeL.comp
        ((sourceIntervalExtensionToBoundary b hp1 hp).comp
          (sourcePeriodicPairCoefficients 1).toContinuousLinearEquiv.toContinuousLinearMap)))

theorem sourceNativeIntervalExtension_coefficients (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    sourcePeriodicPairCoefficients 2 (sourceNativeIntervalExtensionAmbient b hp1 hp u) =
      sourceBoundaryZeroWeightEquiv
        (sourceIntervalExtensionToBoundary b hp1 hp (sourcePeriodicPairCoefficients 1 u)).val :=
  (sourcePeriodicPairCoefficients 2).apply_symm_apply _

theorem sourceNativeIntervalExtension_mem (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    sourceNativeIntervalExtensionAmbient b hp1 hp u ∈ sourceNativeBoundarySubmodule b := by
  change sourcePeriodicPairCoefficients 2 _ ∈ sourceBoundaryBaseSubspace b
  rw [sourceNativeIntervalExtension_coefficients, sourceBoundaryZeroWeightEquiv_mem]
  exact (sourceIntervalExtensionToBoundary b hp1 hp (sourcePeriodicPairCoefficients 1 u)).property

/-- Lemma 4.3 as a map between the original physical-period distribution spaces. -/
def sourceNativeIntervalExtension (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤) :
    SourcePeriodicPair 1 p →L[ℂ] sourceNativeBoundarySubmodule (p := p) b :=
  (sourceNativeIntervalExtensionAmbient b hp1 hp).codRestrict _
    (sourceNativeIntervalExtension_mem b hp1 hp)

theorem norm_sourceNativeIntervalExtension_le (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    ‖sourceNativeIntervalExtension b hp1 hp u‖ ≤
      BoundaryCondition.intervalExtensionBound hp1 hp * ‖u‖ := by
  change ‖(sourcePeriodicPairCoefficients 2).symm
    (sourceBoundaryZeroWeightEquiv
      (sourceIntervalExtensionToBoundary b hp1 hp (sourcePeriodicPairCoefficients 1 u)).val)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  exact (norm_sourceIntervalExtensionToBoundary_le b hp1 hp _).trans_eq
    (congrArg (fun t => BoundaryCondition.intervalExtensionBound hp1 hp * t)
      ((sourcePeriodicPairCoefficients 1).norm_map u))

theorem analyticAt_sourceNativeIntervalExtension (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    AnalyticAt ℂ (sourceNativeIntervalExtension b hp1 hp) u :=
  (sourceNativeIntervalExtension b hp1 hp).analyticAt u

/-- The output amplitude is the actual normalized Fourier coefficient. -/
theorem sourceNativeIntervalExtension_snd (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) (n : ℤ) :
    (sourceNativeIntervalExtension b hp1 hp u).val.snd.val (mode (-n)) =
      sourceIntervalAmplitudeCLM b hp1 hp (sourcePeriodicPairCoefficients 1 u) n := by
  rw [← sourcePeriodicPairCoefficients_snd]
  change (sourcePeriodicPairCoefficients 2
    (sourceNativeIntervalExtensionAmbient b hp1 hp u)).snd n = _
  rw [sourceNativeIntervalExtension_coefficients, sourceBoundaryZeroWeightEquiv_snd,
    sourceIntervalExtensionToBoundary_snd]

/-- The corrected even formula holds on every original input in signed coordinates. -/
theorem sourceNativeIntervalExtension_even (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) (n : ℤ) :
    (sourceNativeIntervalExtension b hp1 hp u).val.snd.val (mode (-(2*n))) =
      ((sourceUnitPeriodSignedCoefficients u).snd n +
        b.extensionSign * (sourceUnitPeriodSignedCoefficients u).fst n) / 2 := by
  rw [sourceNativeIntervalExtension_snd, sourceIntervalAmplitudeCLM_even,
    sourcePeriodicPairCoefficients_eq_signed]
  simp

/-- The native extension has exactly the established actual tempered realization. -/
theorem sourceNativeIntervalExtension_tempered (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    ((sourceNativeIntervalExtension b hp1 hp u).val.fst.val.toTempered,
      (sourceNativeIntervalExtension b hp1 hp u).val.snd.val.toTempered) =
      sourceIntervalExtensionDistributionCLM b hp1 hp (sourcePeriodicPairCoefficients 1 u) := by
  apply Prod.ext
  · apply periodicDistribution_ext
      (sourceNativeIntervalExtension b hp1 hp u).val.fst.val.toTempered_periodic
      (sourceIntervalExtensionDistribution_periodic b hp1 hp _).1
    intro n
    rw [← periodCoefficientTest_two, Distribution.toTempered_coefficient, periodCoefficientTest_two]
    have hc := congrArg (fun a : CoeffPair p => a.fst n)
      (sourceNativeIntervalExtension_coefficients b hp1 hp u)
    rw [sourcePeriodicPairCoefficients_fst, sourceBoundaryZeroWeightEquiv_fst,
      sourceIntervalExtensionToBoundary_fst] at hc
    exact hc.trans (congrArg Prod.fst
      (sourceIntervalExtensionDistribution_coefficients b hp1 hp (sourcePeriodicPairCoefficients 1 u) n)).symm
  · apply periodicDistribution_ext
      (sourceNativeIntervalExtension b hp1 hp u).val.snd.val.toTempered_periodic
      (sourceIntervalExtensionDistribution_periodic b hp1 hp _).2
    intro n
    rw [← periodCoefficientTest_two, Distribution.toTempered_coefficient, periodCoefficientTest_two]
    exact (sourceNativeIntervalExtension_snd b hp1 hp u n).trans
      (congrArg Prod.snd
        (sourceIntervalExtensionDistribution_coefficients b hp1 hp (sourcePeriodicPairCoefficients 1 u) n)).symm


/-- The reflected full signed series converges in the original target norm. -/
theorem hasSum_sourceNativeIntervalExtension (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    HasSum (fun n : ℤ => sourceNativeIntervalExtension b hp1 hp
      (sourceUnitPeriodSignedMode n ((sourceUnitPeriodSignedCoefficients u).fst n)
        ((sourceUnitPeriodSignedCoefficients u).snd n)))
      (sourceNativeIntervalExtension b hp1 hp u) :=
  (sourceNativeIntervalExtension b hp1 hp).hasSum (hasSum_sourceUnitPeriodSignedModes hp u)

/-- Agreement on the actual signed modes determines the entire continuous extension. -/
theorem sourceNativeIntervalExtension_unique (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : SourcePeriodicPair 1 p →L[ℂ] sourceNativeBoundarySubmodule (p := p) b)
    (hF : ∀ n : ℤ, ∀ a c : ℂ, F (sourceUnitPeriodSignedMode n a c) =
      sourceNativeIntervalExtension b hp1 hp (sourceUnitPeriodSignedMode n a c)) :
    F = sourceNativeIntervalExtension b hp1 hp := by
  ext u : 1
  have h := F.hasSum (hasSum_sourceUnitPeriodSignedModes hp u)
  simp only [hF] at h
  exact h.unique (hasSum_sourceNativeIntervalExtension b hp1 hp u)

/-- Signed physical mode inputs have exactly the expected raw finite coordinates. -/
theorem sourceUnitPeriodSignedMode_raw (n : ℤ) (a c : ℂ) :
    sourcePeriodicPairCoefficients 1 (sourceUnitPeriodSignedMode (p := p) n a c) =
      (CoeffPair.toMax p).symm (BoundaryCondition.finitePairCoeffs
        (sourceSignedFinitePair (Finsupp.single n a, Finsupp.single n c))) := by
  rw [sourcePeriodicPairCoefficients_eq_signed]
  have h := sourceUnitPeriodSignedCoefficients.apply_symm_apply
    (WithLp.toLp p (lp.single p n a, lp.single p n c))
  change sourceUnitPeriodSignedCoefficients (sourceUnitPeriodSignedMode n a c) = _ at h
  rw [h]
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> apply lp.ext <;> funext k
  · change Coeff.reflection (lp.single p n a) k = (sourceSignedFinitePair _).1 k
    rw [Coeff.reflection_apply, sourceSignedFinitePair_fst]
    simp [lp.single_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  · change (lp.single p n c : Coeff p) k = (Finsupp.single n c) k
    simp [lp.single_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- The native completed map agrees with the actual physical reflection on each signed mode. -/
theorem sourceNativeIntervalExtension_mode_integrals (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (n k : ℤ) (a c : ℂ) :
    let f := BoundaryCondition.periodOnePair
      (sourceSignedFinitePair (Finsupp.single n a, Finsupp.single n c))
    let F := (sourceNativeIntervalExtension b hp1 hp (sourceUnitPeriodSignedMode n a c)).val
    (F.fst.val (mode (-k)), F.snd.val (mode (-k))) =
      (periodTwoCoefficient (fun x => (BoundaryCondition.intervalExtension b f x).1) k,
        periodTwoCoefficient (fun x => (BoundaryCondition.intervalExtension b f x).2) k) := by
  dsimp only
  rw [← sourcePeriodicPairCoefficients_fst, ← sourcePeriodicPairCoefficients_snd]
  change ((sourcePeriodicPairCoefficients 2 (sourceNativeIntervalExtensionAmbient b hp1 hp _)).fst k,
    (sourcePeriodicPairCoefficients 2 (sourceNativeIntervalExtensionAmbient b hp1 hp _)).snd k) = _
  rw [sourceNativeIntervalExtension_coefficients, sourceBoundaryZeroWeightEquiv_fst,
    sourceBoundaryZeroWeightEquiv_snd, sourceUnitPeriodSignedMode_raw]
  exact sourceIntervalExtensionToBoundary_finite_integrals b hp1 hp _ k


private theorem hasSum_nativeOddKernel (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (n : ℤ) :
    HasSum (fun k : ℤ => a k * (Complex.I / ((Real.pi : ℂ) * (2*k-2*n-1))))
      ((Complex.I / 2 : ℂ) * shiftedHilbertTransform hp1 hp a n) := by
  let q := p.conjExponent
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq1 : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp
    (lt_top_iff_ne_top.mpr hp)
  have hq : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
  have h := ((summable_norm_shiftedHilbertSeries hq1 hq a n).of_norm.hasSum).mul_left
    (Complex.I / 2 : ℂ)
  rw [← shiftedHilbertTransform_apply hp1 hp hq1 hq] at h
  have he : (fun k : ℤ => a k * (Complex.I / ((Real.pi : ℂ) * (2*k-2*n-1)))) =
      (fun k : ℤ => (Complex.I/2 : ℂ) * (a k * (2 / ((Real.pi : ℂ) * (2*k-2*n-1))))) := by
    funext k
    ring
  rw [he]
  exact h

/-- The corrected odd kernel is valid for arbitrary original distributions,
with the full series and literal signed source coefficients. -/
theorem hasSum_sourceNativeIntervalExtension_odd (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) (n : ℤ) :
    HasSum (fun k : ℤ => ((sourceUnitPeriodSignedCoefficients u).snd k -
      b.extensionSign * (sourceUnitPeriodSignedCoefficients u).fst k) *
      (Complex.I / ((Real.pi : ℂ) * (2*k-2*n-1))))
      ((sourceNativeIntervalExtension b hp1 hp u).val.snd.val (mode (-(2*n+1)))) := by
  have hplus := hasSum_nativeOddKernel hp1 hp (sourceUnitPeriodSignedCoefficients u).snd n
  have hminus := (Equiv.neg ℤ).hasSum_iff.mpr
    (hasSum_nativeOddKernel hp1 hp (Coeff.reflection (sourceUnitPeriodSignedCoefficients u).fst) (-n-1))
  have h := hplus.add (hminus.mul_left b.extensionSign)
  convert h using 1
  · funext k
    simp only [Function.comp_apply, Equiv.neg_apply, Coeff.reflection_apply, neg_neg, Int.cast_neg, Int.cast_sub, Int.cast_one]
    have hd : (Real.pi : ℂ) * (2 * -(k : ℂ) - 2 * (-(n : ℂ) - 1) - 1) =
        -((Real.pi : ℂ) * (2*k-2*n-1)) := by ring
    rw [hd, div_neg]
    ring
  · rw [sourceNativeIntervalExtension_snd, sourceIntervalAmplitudeCLM_odd,
      sourcePeriodicPairCoefficients_eq_signed]
    change (Complex.I / 2 : ℂ) *
      (shiftedHilbertTransform hp1 hp (sourceUnitPeriodSignedCoefficients u).snd n +
        b.extensionSign * shiftedHilbertTransform hp1 hp
          (Coeff.reflection (sourceUnitPeriodSignedCoefficients u).fst) (-n-1)) = _
    ring


/-- The actual native boundary spaces are closed in the original finite-p norm. -/
theorem isClosed_sourceNativeBoundarySubmodule (b : BoundaryCondition) :
    IsClosed (sourceNativeBoundarySubmodule (p := p) b : Set (SourcePeriodicPair 2 p)) :=
  (isClosed_sourceBoundaryBaseSubspace b).preimage (sourcePeriodicPairCoefficients 2).continuous

/-- At p=2 the actual native extension preserves the original norm exactly. -/
theorem norm_sourceNativeIntervalExtension_two (b : BoundaryCondition)
    (u : SourcePeriodicPair 1 2) :
    ‖sourceNativeIntervalExtension b (by norm_num) (by simp) u‖ = ‖u‖ := by
  change ‖(sourcePeriodicPairCoefficients 2).symm
    (sourceBoundaryZeroWeightEquiv
      (sourceIntervalExtensionToBoundary b (by norm_num) (by simp)
        (sourcePeriodicPairCoefficients 1 u)).val)‖ = _
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  change ‖sourceIntervalExtensionToBoundary b (by norm_num) (by simp)
    (sourcePeriodicPairCoefficients 1 u)‖ = _
  rw [norm_sourceIntervalExtensionToBoundary_two, LinearIsometryEquiv.norm_map]

end NLS.ZakharovShabat
