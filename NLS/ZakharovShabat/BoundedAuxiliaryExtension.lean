import NLS.ZakharovShabat.BoundedIntervalExtension
import NLS.ZakharovShabat.ClassicalAuxiliarySpectrum
import NLS.SequenceSpaces.PairNorm

/-!
# Bounded source auxiliary eigenfunction extensions

The source extensions in (1.11)–(1.12) are phase conjugates of the completed
ordinary interval maps. Their actual physical Fourier formulas determine them
on finite polynomials and hence uniquely by continuity for every `1 < p < ∞`.
-/

noncomputable section
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The completed period-one to period-two auxiliary eigenfunction extension. -/
def auxiliaryIntervalExtensionCLM (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤) :
    PairSpace p →L[ℂ] PairSpace p :=
  (auxiliaryPhase (Coeff p)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((intervalExtensionCLM b hp hptop).comp
      (auxiliaryPhase (Coeff p)).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem auxiliaryIntervalExtensionCLM_apply (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : PairSpace p) : auxiliaryIntervalExtensionCLM b hp hptop a =
      auxiliaryPhase (Coeff p) (intervalExtensionCLM b hp hptop ((auxiliaryPhase (Coeff p)).symm a)) := rfl

/-- Every completed input lands in the actual auxiliary space. -/
theorem auxiliaryIntervalExtensionCLM_mem (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : PairSpace p) : auxiliaryIntervalExtensionCLM b hp hptop a ∈ auxiliarySpace b :=
  ⟨_, intervalExtensionCLM_mem b hp hptop _, rfl⟩

/-- Phase conjugation retains the same maximum-norm bound for both conditions. -/
theorem norm_auxiliaryIntervalExtensionCLM_apply_le (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : PairSpace p) : ‖auxiliaryIntervalExtensionCLM b hp hptop a‖ ≤ intervalExtensionBound hp hptop * ‖a‖ := by
  rw [auxiliaryIntervalExtensionCLM_apply, LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    norm_intervalExtensionCLM_apply_le b hp hptop ((auxiliaryPhase (Coeff p)).symm a)

theorem norm_auxiliaryIntervalExtensionCLM_le (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤) :
    ‖auxiliaryIntervalExtensionCLM b hp hptop‖ ≤ intervalExtensionBound hp hptop :=
  ContinuousLinearMap.opNorm_le_bound _ (intervalExtensionBound_pos hp hptop).le
    (norm_auxiliaryIntervalExtensionCLM_apply_le b hp hptop)

/-- The second raw coefficient in the source auxiliary Fourier formula. -/
theorem auxiliaryIntervalExtensionCLM_snd (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : PairSpace p) (n : ℤ) : (auxiliaryIntervalExtensionCLM b hp hptop a).2 n =
      halfIntervalCoeffs hp hptop a.2 n + Complex.I * extensionSign b * halfIntervalCoeffs hp hptop a.1 (-n) := by
  change Complex.I * (halfIntervalCoeffs hp hptop (-Complex.I • a.2) n +
    extensionSign b * halfIntervalCoeffs hp hptop a.1 (-n)) = _
  rw [map_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp

/-- The first raw coefficient, with its reflected phase and frequency. -/
theorem auxiliaryIntervalExtensionCLM_fst (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : PairSpace p) (n : ℤ) : (auxiliaryIntervalExtensionCLM b hp hptop a).1 n =
      halfIntervalCoeffs hp hptop a.1 n - Complex.I * extensionSign b * halfIntervalCoeffs hp hptop a.2 (-n) := by
  change extensionSign b * (halfIntervalCoeffs hp hptop (-Complex.I • a.2) (-n) +
    extensionSign b * halfIntervalCoeffs hp hptop a.1 (-(-n))) = _
  rw [map_smul, neg_neg]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  cases b <;> simp [extensionSign]
  ring

/-- Pointwise identification with the folded first component in the printed source extension. -/
theorem auxiliaryIntervalExtension_fst (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) :
    (fun x => (auxiliaryIntervalExtension b f x).1) =
      folded (-Complex.I * extensionSign b) (fun x => (f x).1) (fun x => (f x).2) := by
  funext x
  by_cases hx : x ≤ 1
  · simp [auxiliaryIntervalExtension_left b f x hx, folded, hx]
  · rw [auxiliaryIntervalExtension_right b f x (lt_of_not_ge hx)]
    simp [folded, hx, mul_left_comm, mul_assoc]

/-- Pointwise identification with the folded second component. -/
theorem auxiliaryIntervalExtension_snd (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) :
    (fun x => (auxiliaryIntervalExtension b f x).2) =
      folded (Complex.I * extensionSign b) (fun x => (f x).2) (fun x => (f x).1) := by
  funext x
  by_cases hx : x ≤ 1
  · simp [auxiliaryIntervalExtension_left b f x hx, folded, hx]
  · rw [auxiliaryIntervalExtension_right b f x (lt_of_not_ge hx)]
    simp [folded, hx, mul_left_comm, mul_assoc]

/-- The completed map has exactly the actual physical Fourier integrals on finite period-one polynomials. -/
theorem auxiliaryIntervalExtensionCLM_finite_integrals (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    (periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b (periodOnePair a) x).1) n,
      periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b (periodOnePair a) x).2) n) =
    ((auxiliaryIntervalExtensionCLM b hp hptop (finitePairCoeffs a)).1 n,
      (auxiliaryIntervalExtensionCLM b hp hptop (finitePairCoeffs a)).2 n) := by
  rw [auxiliaryIntervalExtension_fst, auxiliaryIntervalExtension_snd,
    periodTwoCoefficient_folded _ _ _ (continuous_periodOnePair a).fst (continuous_periodOnePair a).snd,
    periodTwoCoefficient_folded _ _ _ (continuous_periodOnePair a).snd (continuous_periodOnePair a).fst,
    auxiliaryIntervalExtensionCLM_fst, auxiliaryIntervalExtensionCLM_snd]
  simp only [finitePairCoeffs_apply, halfIntervalCoeffs_finite_integral, periodOnePair]
  apply Prod.ext <;> ring

/-- The physical finite Fourier formulas uniquely determine the continuous auxiliary extension. -/
theorem auxiliaryIntervalExtensionCLM_unique (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (F : PairSpace p →L[ℂ] PairSpace p)
    (hF : ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ), ∀ n : ℤ,
      ((F (finitePairCoeffs a)).1 n, (F (finitePairCoeffs a)).2 n) =
      (periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b (periodOnePair a) x).1) n,
        periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b (periodOnePair a) x).2) n)) :
    F = auxiliaryIntervalExtensionCLM b hp hptop := by
  apply ContinuousLinearMap.ext
  have he : (F : PairSpace p → PairSpace p) = auxiliaryIntervalExtensionCLM b hp hptop := by
    apply (denseRange_finitePairCoeffs hptop).equalizer F.continuous (auxiliaryIntervalExtensionCLM b hp hptop).continuous
    funext a
    apply Prod.ext <;> ext n
    · exact congrArg Prod.fst ((hF a n).trans (auxiliaryIntervalExtensionCLM_finite_integrals b hp hptop a n))
    · exact congrArg Prod.snd ((hF a n).trans (auxiliaryIntervalExtensionCLM_finite_integrals b hp hptop a n))
  exact congrFun he

/-- The even second coefficients retain the source's half-normalization and both phase signs. -/
theorem auxiliaryIntervalExtensionCLM_snd_even (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : PairSpace p) (n : ℤ) : (auxiliaryIntervalExtensionCLM b hp hptop a).2 (2*n) =
      (a.2 n + Complex.I * extensionSign b * a.1 (-n)) / 2 := by
  rw [auxiliaryIntervalExtensionCLM_snd, show -(2*n) = 2*(-n) by ring,
    halfIntervalCoeffs_even, halfIntervalCoeffs_even]
  ring

/-- The actual Sobolev auxiliary representative also has these same physical Fourier integrals. -/
theorem classicalAuxiliaryExtension_coefficients (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) (n : ℤ) :
    ((classicalAuxiliaryExtension b f hf).1.val n, (classicalAuxiliaryExtension b f hf).2.val n) =
      (periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b f x).1) n,
        periodTwoCoefficient (fun x => (auxiliaryIntervalExtension b f x).2) n) := by
  change ((classicalIntervalExtension b (physicalAuxiliaryPhase.symm f) ((hasClassicalAuxiliaryDomain_iff b f).mp hf)).1.val n,
    Complex.I * (classicalIntervalExtension b (physicalAuxiliaryPhase.symm f) ((hasClassicalAuxiliaryDomain_iff b f).mp hf)).2.val n) =
    (periodTwoCoefficient (fun x => (intervalExtension b (physicalAuxiliaryPhase.symm f) x).1) n,
      periodTwoCoefficient (fun x => Complex.I * (intervalExtension b (physicalAuxiliaryPhase.symm f) x).2) n)
  rw [classicalIntervalExtension_fst, classicalIntervalExtension_snd, periodTwoCoefficient_const_mul]

/-- For finite original auxiliary H¹ input, completion agrees with the original Sobolev extension. -/
theorem auxiliaryIntervalExtensionCLM_finite_eq_classical (b : BoundaryCondition)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (ha : HasClassicalAuxiliaryDomain b (periodOnePair a)) :
    auxiliaryIntervalExtensionCLM b (by norm_num : (1 : ℝ≥0∞) < 2) (by simp) (finitePairCoeffs a) =
      domainInclusion (classicalAuxiliaryExtension b (periodOnePair a) ha) := by
  have he (n : ℤ) := (auxiliaryIntervalExtensionCLM_finite_integrals b
    (by norm_num : (1 : ℝ≥0∞) < 2) (by simp) a n).symm.trans
    (classicalAuxiliaryExtension_coefficients b (periodOnePair a) ha n).symm
  apply Prod.ext <;> ext n
  · simpa only [domainInclusion_apply, scalarInclusion_apply] using congrArg Prod.fst (he n)
  · simpa only [domainInclusion_apply, scalarInclusion_apply] using congrArg Prod.snd (he n)

/-- The lower endpoint obstruction is already present in the actual auxiliary extension of `(0,1)`. -/
theorem not_memlp_auxiliaryIntervalExtension_oneSided (b : BoundaryCondition) :
    ¬Memℓp (fun n => periodTwoCoefficient
      (fun x => (auxiliaryIntervalExtension b (fun _ => ((0 : ℂ), 1)) x).2) n) 1 := by
  have he (n : ℤ) : periodTwoCoefficient
      (fun x => (auxiliaryIntervalExtension b (fun _ => ((0 : ℂ), 1)) x).2) n = overlap 0 n := by
    rw [auxiliaryIntervalExtension_snd, periodTwoCoefficient_folded _ _ _ continuous_const continuous_const]
    simp [halfCoefficient, overlap]
  simpa only [he] using not_memlp_overlap_zero_one

end NLS.ZakharovShabat.BoundaryCondition
