import NLS.ZakharovShabat.BoundedAuxiliaryExtension

/-!
# Auxiliary extensions in the dissertation's pair norm

Both the original period-one input and period-two output carry the actual
component-sum ℓp norm. The target is the closed auxiliary subspace in that norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual auxiliary coefficient space with the dissertation's finite-exponent pair norm. -/
def auxiliarySourceSpace (b : BoundaryCondition) : Submodule ℂ (CoeffPair p) :=
  (auxiliarySpace b).comap (CoeffPair.toMax p).toLinearMap

@[simp] theorem mem_auxiliarySourceSpace (b : BoundaryCondition) (a : CoeffPair p) :
    a ∈ auxiliarySourceSpace b ↔ CoeffPair.toMax p a ∈ auxiliarySpace b := Iff.rfl

theorem isClosed_auxiliarySourceSpace (b : BoundaryCondition) :
    IsClosed (auxiliarySourceSpace (p := p) b : Set (CoeffPair p)) :=
  (isClosed_auxiliarySpace b).preimage (CoeffPair.toMax p).continuous

/-- The source period-one auxiliary extension, retaining the source norm in both ambient spaces. -/
def auxiliarySourceExtension (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤) :
    CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    ((auxiliaryIntervalExtensionCLM b hp hptop).comp (CoeffPair.toMax p).toContinuousLinearMap)

@[simp] theorem toMax_auxiliarySourceExtension (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : CoeffPair p) : CoeffPair.toMax p (auxiliarySourceExtension b hp hptop a) =
      auxiliaryIntervalExtensionCLM b hp hptop (CoeffPair.toMax p a) :=
  (CoeffPair.toMax p).apply_symm_apply _

theorem auxiliarySourceExtension_mem (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : CoeffPair p) : auxiliarySourceExtension b hp hptop a ∈ auxiliarySourceSpace b := by
  rw [mem_auxiliarySourceSpace, toMax_auxiliarySourceExtension]
  exact auxiliaryIntervalExtensionCLM_mem b hp hptop _

/-- A sufficient source-norm bound, including the exact change-of-pair-norm factor. -/
def auxiliarySourceExtensionBound (hp : 1 < p) (hptop : p ≠ ⊤) : ℝ :=
  (2 : ℝ) ^ (1 / p.toReal) * intervalExtensionBound hp hptop

theorem auxiliarySourceExtensionBound_pos (hp : 1 < p) (hptop : p ≠ ⊤) :
    0 < auxiliarySourceExtensionBound hp hptop :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (intervalExtensionBound_pos hp hptop)

/-- Both source extensions are bounded in the literal component-sum norms. -/
theorem norm_auxiliarySourceExtension_apply_le (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : CoeffPair p) : ‖auxiliarySourceExtension b hp hptop a‖ ≤ auxiliarySourceExtensionBound hp hptop * ‖a‖ := by
  change ‖(CoeffPair.toMax p).symm (auxiliaryIntervalExtensionCLM b hp hptop (CoeffPair.toMax p a))‖ ≤ _
  calc
    _ ≤ (2 : ℝ) ^ (1 / p.toReal) * ‖auxiliaryIntervalExtensionCLM b hp hptop (CoeffPair.toMax p a)‖ :=
      CoeffPair.norm_toMax_symm_le hptop _
    _ ≤ (2 : ℝ) ^ (1 / p.toReal) * (intervalExtensionBound hp hptop * ‖CoeffPair.toMax p a‖) := by
      gcongr
      exact norm_auxiliaryIntervalExtensionCLM_apply_le b hp hptop _
    _ ≤ (2 : ℝ) ^ (1 / p.toReal) * (intervalExtensionBound hp hptop * ‖a‖) := by
      gcongr
      · exact (intervalExtensionBound_pos hp hptop).le
      · exact CoeffPair.norm_toMax_le a
    _ = _ := by rw [auxiliarySourceExtensionBound, mul_assoc]

/-- The printed bounded map into the auxiliary source space itself. -/
def auxiliarySourceExtensionToBoundary (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤) :
    CoeffPair p →L[ℂ] auxiliarySourceSpace (p := p) b :=
  (auxiliarySourceExtension b hp hptop).codRestrict _ (auxiliarySourceExtension_mem b hp hptop)

@[simp] theorem auxiliarySourceExtensionToBoundary_coe (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : CoeffPair p) : (auxiliarySourceExtensionToBoundary b hp hptop a : CoeffPair p) =
      auxiliarySourceExtension b hp hptop a := rfl

theorem norm_auxiliarySourceExtensionToBoundary_le (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤) :
    ‖auxiliarySourceExtensionToBoundary b hp hptop‖ ≤ auxiliarySourceExtensionBound hp hptop :=
  ContinuousLinearMap.opNorm_le_bound _ (auxiliarySourceExtensionBound_pos hp hptop).le
    (norm_auxiliarySourceExtension_apply_le b hp hptop)

/-- Bounded complex linearity gives analyticity of the original source extension. -/
theorem analyticAt_auxiliarySourceExtensionToBoundary (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : CoeffPair p) : AnalyticAt ℂ (auxiliarySourceExtensionToBoundary b hp hptop) a :=
  (auxiliarySourceExtensionToBoundary b hp hptop).analyticAt a

/-- Original finite period-one inputs retain both actual Fourier integrals in the source pair norm. -/
theorem auxiliarySourceExtension_finite_integrals (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    let u := auxiliarySourceExtension b hp hptop ((CoeffPair.toMax p).symm (finitePairCoeffs a))
    (u.fst n, u.snd n) =
      (NLS.Fourier.periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b (periodOnePair a) x).1) n,
        NLS.Fourier.periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b (periodOnePair a) x).2) n) := by
  dsimp only
  change ((auxiliaryIntervalExtensionCLM b hp hptop
    (CoeffPair.toMax p ((CoeffPair.toMax p).symm (finitePairCoeffs a)))).1 n,
    (auxiliaryIntervalExtensionCLM b hp hptop
    (CoeffPair.toMax p ((CoeffPair.toMax p).symm (finitePairCoeffs a)))).2 n) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (auxiliaryIntervalExtensionCLM_finite_integrals b hp hptop a n).symm

/-- At the Hilbert exponent the source component-sum norm is preserved exactly. -/
theorem norm_auxiliarySourceExtension_two (b : BoundaryCondition) (a : CoeffPair 2) :
    ‖auxiliarySourceExtension b (by norm_num : (1 : ℝ≥0∞) < 2) (by simp) a‖ = ‖a‖ := by
  let c := (auxiliaryPhase (Coeff 2)).symm (CoeffPair.toMax 2 a)
  let g := intervalExtensionCLM b (by norm_num : (1 : ℝ≥0∞) < 2) (by simp) c
  have hbal : ‖g.1‖ = ‖g.2‖ := by
    change ‖(intervalExtensionCLM b (by norm_num) (by simp) c).1‖ =
      ‖(intervalExtensionCLM b (by norm_num) (by simp) c).2‖
    rw [intervalExtensionCLM_fst, intervalExtensionCLM_snd]
    cases b <;> simp [extensionSign]
  have hg : ‖g‖ ^ 2 = (‖a.fst‖ ^ 2 + ‖a.snd‖ ^ 2) / 2 := by
    dsimp only [g]
    rw [intervalExtensionCLM_two, norm_hilbertIntervalExtension_sq]
    simp [c, norm_smul]
  have ha := norm_withLp_prod_rpow (by simp : (2 : ℝ≥0∞) ≠ ⊤) a
  have ho := norm_withLp_prod_rpow (by simp : (2 : ℝ≥0∞) ≠ ⊤)
    (WithLp.toLp 2 (g.1, Complex.I • g.2))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ha ho
  change ‖WithLp.toLp 2 (g.1, Complex.I • g.2)‖ ^ 2 = ‖g.1‖ ^ 2 + ‖Complex.I • g.2‖ ^ 2 at ho
  simp only [norm_smul, Complex.norm_I, one_mul, hbal] at ho
  rw [Prod.norm_def, hbal, max_self] at hg
  change ‖WithLp.toLp 2 (g.1, Complex.I • g.2)‖ = ‖a‖
  nlinarith [norm_nonneg a, norm_nonneg (WithLp.toLp 2 (g.1, Complex.I • g.2))]

end NLS.ZakharovShabat.BoundaryCondition
