import NLS.ZakharovShabat.SourceLemma42ScalarRestriction

/-! # The literal physical restriction isomorphisms in Lemma 4.2

The domain spaces consist of actual continuous functions on the period-two
circle represented by the printed full trigonometric series. Each element
has classical periodic H1 regularity. Their norm is exactly the physical
Lebesgue H1 norm, constructed through the function/derivative Hilbert embedding.
The scalar restrictions and their inverses are continuous for these physical
norms and act by ordinary restriction on the entire closed interval [0,1].
No extra periodicity or smoothness is required of the interval input.
-/

noncomputable section
open Set NLS.Fourier
namespace NLS.ZakharovShabat
/-- The printed even cosine or odd sine amplitude space. -/
def sourceTrigAmplitudeSpace (sine : Bool) : Submodule ℂ (ScalarDomain 2) :=
  if sine then sourceSineAmplitudeSpace else sourceCosineAmplitudeSpace

def sourceTrigPhase (sine : Bool) : ℂ := if sine then -Complex.I else 1

theorem norm_sourceTrigPhase (sine : Bool) : ‖sourceTrigPhase sine‖ = 1 := by
  cases sine <;> simp [sourceTrigPhase]

def sourceTrigPeriodicSynthesis (sine : Bool) :
    sourceTrigAmplitudeSpace sine →L[ℂ] C(AddCircle (2 : ℝ), ℂ) :=
  sourceTrigPhase sine • (sobolevSynthesis (by simp)).comp (sourceTrigAmplitudeSpace sine).subtypeL

theorem sourceTrigPeriodicSynthesis_eq (sine : Bool) (a : sourceTrigAmplitudeSpace sine) :
    sourceTrigPeriodicSynthesis sine a = sobolevSynthesis (by simp) (sourceTrigPhase sine • a.val) := by
  simp [sourceTrigPeriodicSynthesis]

theorem sourceTrigPeriodicSynthesis_injective (sine : Bool) :
    Function.Injective (sourceTrigPeriodicSynthesis sine) := by
  intro a b h
  rw [sourceTrigPeriodicSynthesis_eq, sourceTrigPeriodicSynthesis_eq] at h
  have hphase : sourceTrigPhase sine ≠ 0 := by
    intro hz
    simpa [hz] using norm_sourceTrigPhase sine
  apply Subtype.ext
  exact smul_right_injective (ScalarDomain 2) hphase (sobolevSynthesis_injective (by simp) h)

/-- Actual periodic functions represented by the printed full trigonometric series. -/
def sourceTrigPeriodicSubmodule (sine : Bool) : Submodule ℂ C(AddCircle (2 : ℝ), ℂ) :=
  LinearMap.range (sourceTrigPeriodicSynthesis sine).toLinearMap

/-- Actual cosine or sine periodic H1 functions, selected by the Boolean parameter. -/
def SourceTrigPeriodicH1 (sine : Bool) := ↥(sourceTrigPeriodicSubmodule sine)

instance (sine : Bool) : AddCommGroup (SourceTrigPeriodicH1 sine) :=
  inferInstanceAs (AddCommGroup ↥(sourceTrigPeriodicSubmodule sine))
instance (sine : Bool) : Module ℂ (SourceTrigPeriodicH1 sine) :=
  inferInstanceAs (Module ℂ ↥(sourceTrigPeriodicSubmodule sine))

def sourceTrigPeriodicLinearEquiv (sine : Bool) :
    sourceTrigAmplitudeSpace sine ≃ₗ[ℂ] SourceTrigPeriodicH1 sine :=
  LinearEquiv.ofInjective (sourceTrigPeriodicSynthesis sine).toLinearMap
    (sourceTrigPeriodicSynthesis_injective sine)

private def sourceTrigEnergyEmbedding (sine : Bool) :
    SourceTrigPeriodicH1 sine →ₗ[ℂ] WithLp 2 (CircleL2 × CircleL2) :=
  sobolevEnergyEmbedding.comp ((sourceTrigPhase sine • (sourceTrigAmplitudeSpace sine).subtype).comp
    (sourceTrigPeriodicLinearEquiv sine).symm.toLinearMap)

private theorem sourceTrigEnergyEmbedding_injective (sine : Bool) :
    Function.Injective (sourceTrigEnergyEmbedding sine) := by
  intro f g h
  have hphase : sourceTrigPhase sine ≠ 0 := by
    intro hz
    simpa [hz] using norm_sourceTrigPhase sine
  apply (sourceTrigPeriodicLinearEquiv sine).symm.injective
  apply Subtype.ext
  exact smul_right_injective (ScalarDomain 2) hphase (sobolevEnergyEmbedding_injective h)

instance (sine : Bool) : NormedAddCommGroup (SourceTrigPeriodicH1 sine) :=
  NormedAddCommGroup.induced _ _ (sourceTrigEnergyEmbedding sine)
    (sourceTrigEnergyEmbedding_injective sine)
instance (sine : Bool) : NormedSpace ℂ (SourceTrigPeriodicH1 sine) :=
  NormedSpace.induced ℂ _ _ (sourceTrigEnergyEmbedding sine)

theorem sourceTrigPeriodic_regular (sine : Bool) (f : SourceTrigPeriodicH1 sine) :
    HasPeriodicH1Regularity f.val := by
  obtain ⟨a,ha⟩ := f.property
  change sourceTrigPeriodicSynthesis sine a = f.val at ha
  rw [← ha, sourceTrigPeriodicSynthesis_eq]
  exact hasPeriodicH1Regularity_sobolevSynthesis _

/-- The function-space norm is exactly the ordinary periodic H1 norm. -/
theorem norm_sourceTrigPeriodicH1 (sine : Bool) (f : SourceTrigPeriodicH1 sine) :
    ‖f‖ = Real.sqrt (intervalH1Energy (fun x : ℝ => f.val (x : AddCircle (2 : ℝ))) 0 2) := by
  change ‖sobolevEnergyEmbedding
    (sourceTrigPhase sine • ((sourceTrigPeriodicLinearEquiv sine).symm f).val)‖ = _
  rw [norm_sobolevEnergyEmbedding, ← sourceTrigPeriodicSynthesis_eq]
  have h := congrArg Subtype.val ((sourceTrigPeriodicLinearEquiv sine).apply_symm_apply f)
  change sourceTrigPeriodicSynthesis sine ((sourceTrigPeriodicLinearEquiv sine).symm f) = f.val at h
  rw [h]

theorem sourceTrigPeriodic_norm_bounds (sine : Bool) (a : sourceTrigAmplitudeSpace sine) :
    ‖a‖ ≤ ‖sourceTrigPeriodicLinearEquiv sine a‖ ∧
      ‖sourceTrigPeriodicLinearEquiv sine a‖ ≤ Real.sqrt 2 * Real.pi * ‖a‖ := by
  have he := intervalH1Energy_sobolevSynthesis_bounds (sourceTrigPhase sine • a.val)
  rw [← norm_sq_sobolevEnergyEmbedding] at he
  have hn : ‖sourceTrigPhase sine • a.val‖ = ‖a‖ := by
    rw [norm_smul, norm_sourceTrigPhase, one_mul]
    rfl
  rw [hn] at he
  have hv : sourceTrigEnergyEmbedding sine (sourceTrigPeriodicLinearEquiv sine a) =
      sobolevEnergyEmbedding (sourceTrigPhase sine • a.val) := by
    change sobolevEnergyEmbedding (sourceTrigPhase sine •
      ((sourceTrigPeriodicLinearEquiv sine).symm (sourceTrigPeriodicLinearEquiv sine a)).val) = _
    rw [LinearEquiv.symm_apply_apply]
  change ‖a‖ ≤ ‖sourceTrigEnergyEmbedding sine (sourceTrigPeriodicLinearEquiv sine a)‖ ∧ _
  rw [hv]
  change _ ∧ ‖sourceTrigEnergyEmbedding sine (sourceTrigPeriodicLinearEquiv sine a)‖ ≤ _
  rw [hv]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hc : 0 ≤ Real.sqrt 2 * Real.pi * ‖a‖ := by positivity
  constructor <;> nlinarith [norm_nonneg a,
    norm_nonneg (sobolevEnergyEmbedding (sourceTrigPhase sine • a.val))]

/-- Actual periodic H1 functions and their unique amplitudes have equivalent norms. -/
def sourceTrigPeriodicEquiv (sine : Bool) :
    sourceTrigAmplitudeSpace sine ≃L[ℂ] SourceTrigPeriodicH1 sine :=
  (sourceTrigPeriodicLinearEquiv sine).toContinuousLinearEquivOfBounds (Real.sqrt 2 * Real.pi) 1
    (fun a => (sourceTrigPeriodic_norm_bounds sine a).2)
    (fun f => by
      simpa only [LinearEquiv.apply_symm_apply, one_mul] using
        (sourceTrigPeriodic_norm_bounds sine ((sourceTrigPeriodicLinearEquiv sine).symm f)).1)

theorem sourceTrigPeriodicEquiv_cosine (b : sourceCosineAmplitudeSpace (p := 2)) :
    (sourceTrigPeriodicEquiv false b).val = sourceCosineSynthesis (by simp) b.val := by
  calc
    _ = sobolevSynthesis (by simp) (sourceTrigPhase false • b.val) :=
      sourceTrigPeriodicSynthesis_eq false b
    _ = sobolevSynthesis (by simp) b.val := by simp [sourceTrigPhase]
    _ = _ := (sourceCosineSynthesis_of_even (by simp) b.val
      ((mem_sourceCosineAmplitudeSpace b.val).mp b.property)).symm

theorem sourceTrigPeriodicEquiv_sine (a : sourceSineAmplitudeSpace (p := 2)) :
    (sourceTrigPeriodicEquiv true a).val = sourceSineSynthesis (by simp) a.val := by
  calc
    _ = sobolevSynthesis (by simp) (sourceTrigPhase true • a.val) :=
      sourceTrigPeriodicSynthesis_eq true a
    _ = -Complex.I • sobolevSynthesis (by simp) a.val := by simp [sourceTrigPhase]
    _ = _ := (sourceSineSynthesis_of_odd (by simp) a.val
      ((mem_sourceSineAmplitudeSpace a.val).mp a.property)).symm

/-- The actual cosine function space is exactly the space of full even-amplitude series. -/
theorem mem_sourceCosinePeriodic_iff (f : C(AddCircle (2 : ℝ), ℂ)) :
    f ∈ sourceTrigPeriodicSubmodule false ↔ ∃ b : sourceCosineAmplitudeSpace (p := 2),
      HasSum (fun n : ℤ => b.val.val n • sourceCosineMode n) f := by
  constructor
  · rintro ⟨b,hb⟩
    change (sourceTrigPeriodicEquiv false b).val = f at hb
    have he := (sourceTrigPeriodicEquiv_cosine b).symm.trans hb
    exact ⟨b,he ▸ hasSum_sourceCosineSynthesis (by simp) b.val⟩
  · rintro ⟨b,hb⟩
    refine ⟨b,?_⟩
    change (sourceTrigPeriodicEquiv false b).val = f
    exact (sourceTrigPeriodicEquiv_cosine b).trans
      ((hasSum_sourceCosineSynthesis (by simp) b.val).unique hb)

/-- The actual sine function space is exactly the space of full odd-amplitude series. -/
theorem mem_sourceSinePeriodic_iff (f : C(AddCircle (2 : ℝ), ℂ)) :
    f ∈ sourceTrigPeriodicSubmodule true ↔ ∃ a : sourceSineAmplitudeSpace (p := 2),
      HasSum (fun n : ℤ => a.val.val n • sourceSineMode n) f := by
  constructor
  · rintro ⟨a,ha⟩
    change (sourceTrigPeriodicEquiv true a).val = f at ha
    have he := (sourceTrigPeriodicEquiv_sine a).symm.trans ha
    exact ⟨a,he ▸ hasSum_sourceSineSynthesis (by simp) a.val⟩
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    change (sourceTrigPeriodicEquiv true a).val = f
    exact (sourceTrigPeriodicEquiv_sine a).trans
      ((hasSum_sourceSineSynthesis (by simp) a.val).unique ha)

/-- The printed R_cos on actual periodic functions, with physical H1 norms on both sides. -/
def sourcePhysicalCosineRestriction : SourceTrigPeriodicH1 false ≃L[ℂ] SourceScalarIntervalH1 false :=
  (sourceTrigPeriodicEquiv false).symm.trans sourceCosineRestrictionEquiv

/-- The printed R_sin on actual periodic functions, with physical H1 norms on both sides. -/
def sourcePhysicalSineRestriction : SourceTrigPeriodicH1 true ≃L[ℂ] SourceScalarIntervalH1 true :=
  (sourceTrigPeriodicEquiv true).symm.trans sourceSineRestrictionEquiv

theorem sourcePhysicalCosineRestriction_apply (f : SourceTrigPeriodicH1 false)
    (x : Icc (0 : ℝ) 1) :
    (sourcePhysicalCosineRestriction f).val x = f.val (x.val : AddCircle (2 : ℝ)) := by
  let a : sourceCosineAmplitudeSpace (p := 2) := (sourceTrigPeriodicEquiv false).symm f
  have he := congrArg Subtype.val ((sourceTrigPeriodicEquiv false).apply_symm_apply f)
  have he' := (sourceTrigPeriodicEquiv_cosine a).symm.trans he
  change (sourceCosineRestrictionEquiv a).val x = _
  rw [sourceCosineRestrictionEquiv_apply]
  exact congrArg (fun u : C(AddCircle (2 : ℝ), ℂ) => u (x.val : AddCircle (2 : ℝ))) he'

theorem sourcePhysicalSineRestriction_apply (f : SourceTrigPeriodicH1 true)
    (x : Icc (0 : ℝ) 1) :
    (sourcePhysicalSineRestriction f).val x = f.val (x.val : AddCircle (2 : ℝ)) := by
  let a : sourceSineAmplitudeSpace (p := 2) := (sourceTrigPeriodicEquiv true).symm f
  have he := congrArg Subtype.val ((sourceTrigPeriodicEquiv true).apply_symm_apply f)
  have he' := (sourceTrigPeriodicEquiv_sine a).symm.trans he
  change (sourceSineRestrictionEquiv a).val x = _
  rw [sourceSineRestrictionEquiv_apply]
  exact congrArg (fun u : C(AddCircle (2 : ℝ), ℂ) => u (x.val : AddCircle (2 : ℝ))) he'

/-- The exact product-domain identity in the proof of Lemma 4.2. -/
def sourcePhysicalTrigClassicalEquiv :
    (SourceTrigPeriodicH1 false × SourceTrigPeriodicH1 true) ≃L[ℂ]
      BoundaryCondition.ClassicalIntervalDomain .dirichlet :=
  (sourcePhysicalCosineRestriction.prodCongr sourcePhysicalSineRestriction).trans
    sourceScalarProductClassicalEquiv

theorem sourcePhysicalTrigClassicalEquiv_apply
    (f : SourceTrigPeriodicH1 false) (g : SourceTrigPeriodicH1 true) (x : Icc (0 : ℝ) 1) :
    (sourcePhysicalTrigClassicalEquiv (f,g)).val x =
      aknsToZS (f.val (x.val : AddCircle (2 : ℝ)),g.val (x.val : AddCircle (2 : ℝ))) := by
  change (sourceScalarProductClassicalEquiv
    (sourcePhysicalCosineRestriction f,sourcePhysicalSineRestriction g)).val x = _
  rw [sourceScalarProductClassicalEquiv_apply, sourcePhysicalCosineRestriction_apply,
    sourcePhysicalSineRestriction_apply]

end NLS.ZakharovShabat


