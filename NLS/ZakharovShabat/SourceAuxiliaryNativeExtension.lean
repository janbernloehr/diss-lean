import NLS.ZakharovShabat.SourceLemma43NativeExtension
import NLS.ZakharovShabat.SourceAuxiliaryExtensionPhysical

/-! # Auxiliary reflection on the original periodic distributions

The Section 5 extensions act on native smooth-test distributions at the
physical periods one and two. Their closed targets retain the auxiliary
phase relation. For 1<p<infinity, the maps are bounded and analytic in the
original norms, agree with physical Fourier integrals on signed modes, and
are uniquely determined by those modes. The full reflected signed series
converges in the target norm. At p=2 the map is an isometry and agrees with
physical reflection on arbitrary L2 input. No endpoint extension is asserted.
-/

noncomputable section
open scoped ENNReal SchwartzMap
open NLS NLS.Fourier NLS.Fourier.SmoothPeriodicTest
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The auxiliary boundary condition on actual period-two distributions. -/
def sourceNativeAuxiliarySubmodule (b : BoundaryCondition) :
    Submodule ℂ (SourcePeriodicPair 2 p) :=
  (BoundaryCondition.auxiliarySourceSpace b).comap (sourcePeriodicPairCoefficients 2).toLinearMap

theorem mem_sourceNativeAuxiliarySubmodule (b : BoundaryCondition) (u : SourcePeriodicPair 2 p) :
    u ∈ sourceNativeAuxiliarySubmodule b ↔
      ∀ n : ℤ, u.fst.val (mode (-n)) = -Complex.I * b.extensionSign * u.snd.val (mode n) := by
  change CoeffPair.toMax p (sourcePeriodicPairCoefficients 2 u) ∈ BoundaryCondition.auxiliarySpace b ↔ _
  cases b
  · rw [BoundaryCondition.mem_auxiliaryDirichletSpace]
    change (∀ n, (sourcePeriodicPairCoefficients 2 u).fst n =
      -Complex.I * (sourcePeriodicPairCoefficients 2 u).snd (-n)) ↔ _
    simp only [sourcePeriodicPairCoefficients_fst, sourcePeriodicPairCoefficients_snd,
      neg_neg, BoundaryCondition.extensionSign, mul_one]
  · rw [BoundaryCondition.mem_auxiliaryNeumannSpace]
    change (∀ n, (sourcePeriodicPairCoefficients 2 u).fst n =
      Complex.I * (sourcePeriodicPairCoefficients 2 u).snd (-n)) ↔ _
    simp only [sourcePeriodicPairCoefficients_fst, sourcePeriodicPairCoefficients_snd,
      neg_neg, BoundaryCondition.extensionSign, mul_neg_one]

theorem isClosed_sourceNativeAuxiliarySubmodule (b : BoundaryCondition) :
    IsClosed (sourceNativeAuxiliarySubmodule (p := p) b : Set (SourcePeriodicPair 2 p)) :=
  (BoundaryCondition.isClosed_auxiliarySourceSpace b).preimage (sourcePeriodicPairCoefficients 2).continuous

/-- Completed auxiliary reflection at the original physical periods. -/
def sourceNativeAuxiliaryExtensionAmbient (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤) :
    SourcePeriodicPair 1 p →L[ℂ] SourcePeriodicPair 2 p :=
  (sourcePeriodicPairCoefficients 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((BoundaryCondition.auxiliarySourceExtension b hp1 hp).comp
      (sourcePeriodicPairCoefficients 1).toContinuousLinearEquiv.toContinuousLinearMap)

theorem sourceNativeAuxiliaryExtension_coefficients (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    sourcePeriodicPairCoefficients 2 (sourceNativeAuxiliaryExtensionAmbient b hp1 hp u) =
      BoundaryCondition.auxiliarySourceExtension b hp1 hp (sourcePeriodicPairCoefficients 1 u) :=
  (sourcePeriodicPairCoefficients 2).apply_symm_apply _

theorem sourceNativeAuxiliaryExtension_mem (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    sourceNativeAuxiliaryExtensionAmbient b hp1 hp u ∈ sourceNativeAuxiliarySubmodule b := by
  change sourcePeriodicPairCoefficients 2 _ ∈ BoundaryCondition.auxiliarySourceSpace b
  rw [sourceNativeAuxiliaryExtension_coefficients]
  exact BoundaryCondition.auxiliarySourceExtension_mem b hp1 hp _

/-- The Section 5 map into its actual closed native auxiliary boundary space. -/
def sourceNativeAuxiliaryExtension (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤) :
    SourcePeriodicPair 1 p →L[ℂ] sourceNativeAuxiliarySubmodule (p := p) b :=
  (sourceNativeAuxiliaryExtensionAmbient b hp1 hp).codRestrict _
    (sourceNativeAuxiliaryExtension_mem b hp1 hp)

/-- Native reflection and the previously completed Fourier operator are identical. -/
theorem sourceNativeAuxiliaryExtension_raw (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    sourcePeriodicPairCoefficients 2 (sourceNativeAuxiliaryExtension b hp1 hp u).val =
      sourceBoundaryZeroWeightEquiv
        (sourceAuxiliaryExtensionToBoundary b hp1 hp (sourcePeriodicPairCoefficients 1 u)).val := by
  change sourcePeriodicPairCoefficients 2 (sourceNativeAuxiliaryExtensionAmbient b hp1 hp u) = _
  rw [sourceNativeAuxiliaryExtension_coefficients, sourceAuxiliaryExtensionToBoundary_eq_completed]

theorem norm_sourceNativeAuxiliaryExtension_le (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    ‖sourceNativeAuxiliaryExtension b hp1 hp u‖ ≤
      BoundaryCondition.intervalExtensionBound hp1 hp * ‖u‖ := by
  change ‖(sourcePeriodicPairCoefficients 2).symm
    (BoundaryCondition.auxiliarySourceExtension b hp1 hp (sourcePeriodicPairCoefficients 1 u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (norm_auxiliarySourceExtension_improved_le b hp1 hp _).trans_eq
    (congrArg (fun t => BoundaryCondition.intervalExtensionBound hp1 hp * t)
      ((sourcePeriodicPairCoefficients 1).norm_map u))

theorem analyticAt_sourceNativeAuxiliaryExtension (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    AnalyticAt ℂ (sourceNativeAuxiliaryExtension b hp1 hp) u :=
  (sourceNativeAuxiliaryExtension b hp1 hp).analyticAt u

/-- Actual normalized output coefficients retain both the auxiliary phase and sign. -/
theorem sourceNativeAuxiliaryExtension_fourier (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) (n : ℤ) :
    let F := (sourceNativeAuxiliaryExtension b hp1 hp u).val
    (F.fst.val (mode (-n)), F.snd.val (mode (-n))) =
      (b.extensionSign * sourceAuxiliaryIntervalAmplitudeCLM b hp1 hp
        (sourcePeriodicPairCoefficients 1 u) (-n),
        Complex.I * sourceAuxiliaryIntervalAmplitudeCLM b hp1 hp (sourcePeriodicPairCoefficients 1 u) n) := by
  dsimp only
  rw [← sourcePeriodicPairCoefficients_fst, ← sourcePeriodicPairCoefficients_snd,
    sourceNativeAuxiliaryExtension_raw, sourceBoundaryZeroWeightEquiv_fst,
    sourceBoundaryZeroWeightEquiv_snd, sourceAuxiliaryExtensionToBoundary_fst,
    sourceAuxiliaryExtensionToBoundary_snd]

/-- The even coefficients retain the half normalization and the auxiliary phase. -/
theorem sourceNativeAuxiliaryExtension_even (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) (n : ℤ) :
    (sourceNativeAuxiliaryExtension b hp1 hp u).val.snd.val (mode (-(2*n))) =
      ((sourceUnitPeriodSignedCoefficients u).snd n +
        Complex.I * b.extensionSign * (sourceUnitPeriodSignedCoefficients u).fst n) / 2 := by
  have h := congrArg Prod.snd (sourceNativeAuxiliaryExtension_fourier b hp1 hp u (2*n))
  dsimp only at h
  rw [h]
  change Complex.I * sourceIntervalAmplitudeCLM b hp1 hp
    ((sourceAuxiliaryInputPhase hp).symm (sourcePeriodicPairCoefficients 1 u)) (2*n) = _
  rw [sourceIntervalAmplitudeCLM_even, sourcePeriodicPairCoefficients_eq_signed]
  change Complex.I * ((-Complex.I * (sourceUnitPeriodSignedCoefficients u).snd n +
    b.extensionSign * Coeff.reflection (sourceUnitPeriodSignedCoefficients u).fst (-n)) / 2) = _
  rw [Coeff.reflection_apply, neg_neg]
  ring_nf
  simp
  ring

/-- The complete reflected signed-mode series converges in the original target norm. -/
theorem hasSum_sourceNativeAuxiliaryExtension (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    HasSum (fun n : ℤ => sourceNativeAuxiliaryExtension b hp1 hp
      (sourceUnitPeriodSignedMode n ((sourceUnitPeriodSignedCoefficients u).fst n)
        ((sourceUnitPeriodSignedCoefficients u).snd n)))
      (sourceNativeAuxiliaryExtension b hp1 hp u) :=
  (sourceNativeAuxiliaryExtension b hp1 hp).hasSum (hasSum_sourceUnitPeriodSignedModes hp u)

/-- Physical signed modes uniquely determine the bounded extension on all rough input. -/
theorem sourceNativeAuxiliaryExtension_unique (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : SourcePeriodicPair 1 p →L[ℂ] sourceNativeAuxiliarySubmodule (p := p) b)
    (hF : ∀ n : ℤ, ∀ a c : ℂ, F (sourceUnitPeriodSignedMode n a c) =
      sourceNativeAuxiliaryExtension b hp1 hp (sourceUnitPeriodSignedMode n a c)) :
    F = sourceNativeAuxiliaryExtension b hp1 hp := by
  ext u : 1
  have h := F.hasSum (hasSum_sourceUnitPeriodSignedModes hp u)
  simp only [hF] at h
  exact h.unique (hasSum_sourceNativeAuxiliaryExtension b hp1 hp u)

/-- The native map agrees with the literal physical auxiliary reflection on signed modes. -/
theorem sourceNativeAuxiliaryExtension_mode_integrals (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (n k : ℤ) (a c : ℂ) :
    let f := BoundaryCondition.periodOnePair
      (sourceSignedFinitePair (Finsupp.single n a, Finsupp.single n c))
    let F := (sourceNativeAuxiliaryExtension b hp1 hp (sourceUnitPeriodSignedMode n a c)).val
    (F.fst.val (mode (-k)), F.snd.val (mode (-k))) =
      (periodTwoCoefficient (fun x => (BoundaryCondition.auxiliaryIntervalExtension b f x).1) k,
        periodTwoCoefficient (fun x => (BoundaryCondition.auxiliaryIntervalExtension b f x).2) k) := by
  dsimp only
  rw [← sourcePeriodicPairCoefficients_fst, ← sourcePeriodicPairCoefficients_snd,
    sourceNativeAuxiliaryExtension_raw, sourceBoundaryZeroWeightEquiv_fst,
    sourceBoundaryZeroWeightEquiv_snd, sourceUnitPeriodSignedMode_raw]
  exact sourceAuxiliaryExtensionToBoundary_finite_integrals b hp1 hp _ k

/-- At p=2 auxiliary native reflection preserves the exact source norm. -/
theorem norm_sourceNativeAuxiliaryExtension_two (b : BoundaryCondition) (u : SourcePeriodicPair 1 2) :
    ‖sourceNativeAuxiliaryExtension b (by norm_num) (by simp) u‖ = ‖u‖ := by
  change ‖(sourcePeriodicPairCoefficients 2).symm
    (BoundaryCondition.auxiliarySourceExtension b (by norm_num) (by simp)
      (sourcePeriodicPairCoefficients 1 u))‖ = _
  rw [LinearIsometryEquiv.norm_map, BoundaryCondition.norm_auxiliarySourceExtension_two,
    LinearIsometryEquiv.norm_map]

/-- The native and tempered realizations agree on every rough input. -/
theorem sourceNativeAuxiliaryExtension_tempered (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    ((sourceNativeAuxiliaryExtension b hp1 hp u).val.fst.val.toTempered,
      (sourceNativeAuxiliaryExtension b hp1 hp u).val.snd.val.toTempered) =
      sourceAuxiliaryExtensionDistributionCLM b hp1 hp (sourcePeriodicPairCoefficients 1 u) := by
  have hper : IsPeriodTwoDistribution
      (sourceAuxiliaryExtensionDistributionCLM b hp1 hp (sourcePeriodicPairCoefficients 1 u)).1 ∧
      IsPeriodTwoDistribution
        (sourceAuxiliaryExtensionDistributionCLM b hp1 hp (sourcePeriodicPairCoefficients 1 u)).2 :=
    ⟨isPeriodTwoDistribution_weightedDistributionSynthesis _ _ _,
      isPeriodTwoDistribution_weightedDistributionSynthesis _ _ _⟩
  apply Prod.ext
  · apply periodicDistribution_ext
      (sourceNativeAuxiliaryExtension b hp1 hp u).val.fst.val.toTempered_periodic hper.1
    intro n
    rw [← periodCoefficientTest_two, Distribution.toTempered_coefficient, periodCoefficientTest_two]
    exact (congrArg Prod.fst (sourceNativeAuxiliaryExtension_fourier b hp1 hp u n)).trans
      (congrArg Prod.fst (sourceAuxiliaryExtensionDistribution_coefficients b hp1 hp
        (sourcePeriodicPairCoefficients 1 u) n)).symm
  · apply periodicDistribution_ext
      (sourceNativeAuxiliaryExtension b hp1 hp u).val.snd.val.toTempered_periodic hper.2
    intro n
    rw [← periodCoefficientTest_two, Distribution.toTempered_coefficient, periodCoefficientTest_two]
    exact (congrArg Prod.snd (sourceNativeAuxiliaryExtension_fourier b hp1 hp u n)).trans
      (congrArg Prod.snd (sourceAuxiliaryExtensionDistribution_coefficients b hp1 hp
        (sourcePeriodicPairCoefficients 1 u) n)).symm

/-- For arbitrary L2 data, native reflection has exactly the physical Fourier coefficients. -/
theorem sourceNativeAuxiliaryExtension_two_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 1))) :
    sourcePeriodicPairCoefficients 2 (sourceNativeAuxiliaryExtension b (by norm_num) (by simp)
      ((sourcePeriodicPairCoefficients 1).symm (sourceUnitIntervalL2Coefficients f hf))).val =
      sourceAuxiliaryIntervalExtensionCoefficients b f hf := by
  rw [sourceNativeAuxiliaryExtension_raw, LinearIsometryEquiv.apply_symm_apply,
    sourceAuxiliaryExtensionToBoundary_two_ofFunction]

/-- L2 synthesis of native reflection is the actual phase-twisted reflected function. -/
theorem sourceNativeAuxiliaryExtension_two_physical (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 1))) :
    sourceCircleRepresentative (sourceCircleSynthesis (sourcePeriodicPairCoefficients 2
      (sourceNativeAuxiliaryExtension b (by norm_num) (by simp)
        ((sourcePeriodicPairCoefficients 1).symm (sourceUnitIntervalL2Coefficients f hf))).val))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 2)] BoundaryCondition.auxiliaryIntervalExtension b f := by
  rw [sourceNativeAuxiliaryExtension_two_ofFunction]
  exact sourceCircleSynthesis_auxiliaryIntervalExtension b f hf

end NLS.ZakharovShabat
