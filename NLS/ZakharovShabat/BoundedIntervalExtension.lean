import NLS.Fourier.HalfIntervalBoundedness

/-!
# Bounded Dirichlet and Neumann interval extensions

The half-interval map and signed reflection give the coefficient form of
Lemma 4.3 for every `1<p<∞`. The operators agree with the physical Fourier
integrals on finite polynomials, land in the actual boundary spaces, and are
unique continuous extensions. Fourier/distribution and Sobolev realizations
remain separate from this coefficient theorem.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.BoundaryCondition
open NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)

/-- Completed boundary amplitudes of period-one coefficient pairs. -/
def intervalAmplitudeCLM : PairSpace p →L[ℂ] Coeff p :=
  (halfIntervalCoeffs hp hptop).comp (ContinuousLinearMap.snd ℂ _ _) +
    extensionSign b • (((Coeff.reflection (p := p)).toContinuousLinearEquiv.toContinuousLinearMap.comp (halfIntervalCoeffs hp hptop)).comp
      (ContinuousLinearMap.fst ℂ _ _))

/-- The full-range period-two interval extension in the ambient pair space. -/
def intervalExtensionCLM : PairSpace p →L[ℂ] PairSpace p :=
  ((extensionSign b • (Coeff.reflection (p := p)).toContinuousLinearEquiv.toContinuousLinearMap).comp
    (intervalAmplitudeCLM b hp hptop)).prod (intervalAmplitudeCLM b hp hptop)

@[simp] theorem intervalExtensionCLM_snd (a : PairSpace p) :
    (intervalExtensionCLM b hp hptop a).2 = intervalAmplitudeCLM b hp hptop a := rfl

@[simp] theorem intervalExtensionCLM_fst (a : PairSpace p) :
    (intervalExtensionCLM b hp hptop a).1 =
      extensionSign b • Coeff.reflection (intervalAmplitudeCLM b hp hptop a) := rfl

/-- The complete ambient output is determined by its boundary amplitude. -/
theorem norm_intervalExtensionCLM (a : PairSpace p) :
    ‖intervalExtensionCLM b hp hptop a‖ = ‖intervalAmplitudeCLM b hp hptop a‖ := by
  change ‖(extensionSign b • Coeff.reflection (intervalAmplitudeCLM b hp hptop a),
    intervalAmplitudeCLM b hp hptop a)‖ = _
  cases b <;> simp [extensionSign, Prod.norm_def]

/-- The amplitude estimate retains separate norms of the two original components. -/
theorem norm_intervalAmplitudeCLM_le (a : PairSpace p) :
    ‖intervalAmplitudeCLM b hp hptop a‖ ≤ halfIntervalBound hp hptop * (‖a.1‖ + ‖a.2‖) := by
  change ‖halfIntervalCoeffs hp hptop a.2 +
    extensionSign b • Coeff.reflection (halfIntervalCoeffs hp hptop a.1)‖ ≤ _
  have hs : ‖extensionSign b‖ = 1 := by cases b <;> simp [extensionSign]
  calc
    _ ≤ ‖halfIntervalCoeffs hp hptop a.2‖ +
        ‖extensionSign b • Coeff.reflection (halfIntervalCoeffs hp hptop a.1)‖ := norm_add_le _ _
    _ = ‖halfIntervalCoeffs hp hptop a.2‖ + ‖halfIntervalCoeffs hp hptop a.1‖ := by
      rw [norm_smul, hs, one_mul, Coeff.reflection.norm_map]
    _ ≤ halfIntervalBound hp hptop * ‖a.2‖ + halfIntervalBound hp hptop * ‖a.1‖ :=
      add_le_add (norm_halfIntervalCoeffs_apply_le hp hptop _) (norm_halfIntervalCoeffs_apply_le hp hptop _)
    _ = _ := by ring

/-- One constant works for both boundary conditions in the maximum pair norm. -/
def intervalExtensionBound : ℝ := 2 * halfIntervalBound hp hptop

theorem intervalExtensionBound_pos : 0 < intervalExtensionBound hp hptop :=
  mul_pos (by norm_num) (halfIntervalBound_pos hp hptop)

theorem norm_intervalExtensionCLM_apply_le (a : PairSpace p) :
    ‖intervalExtensionCLM b hp hptop a‖ ≤ intervalExtensionBound hp hptop * ‖a‖ := by
  rw [norm_intervalExtensionCLM]
  apply (norm_intervalAmplitudeCLM_le b hp hptop a).trans
  have h₁ := norm_fst_le a
  have h₂ := norm_snd_le a
  have h := halfIntervalBound_pos hp hptop
  unfold intervalExtensionBound
  nlinarith

theorem norm_intervalExtensionCLM_le : ‖intervalExtensionCLM b hp hptop‖ ≤ intervalExtensionBound hp hptop :=
  ContinuousLinearMap.opNorm_le_bound _ (intervalExtensionBound_pos hp hptop).le
    (norm_intervalExtensionCLM_apply_le b hp hptop)

/-- The constructed amplitude agrees with the earlier finite physical map. -/
theorem intervalAmplitudeCLM_finite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    intervalAmplitudeCLM b hp hptop (finitePairCoeffs a) = finiteIntervalAmplitude b hp a := by
  change halfIntervalCoeffs hp hptop (Coeff.ofFinsupp a.2) +
    extensionSign b • Coeff.reflection (halfIntervalCoeffs hp hptop (Coeff.ofFinsupp a.1)) =
      polynomialHalfCoeffs hp a.2 + extensionSign b • Coeff.reflection (polynomialHalfCoeffs hp a.1)
  rw [halfIntervalCoeffs_finite, halfIntervalCoeffs_finite]

/-- The whole completed map agrees with the finite Fourier extension. -/
theorem intervalExtensionCLM_finite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    intervalExtensionCLM b hp hptop (finitePairCoeffs a) = finiteIntervalExtension b hp a := by
  apply Prod.ext
  · simp only [intervalExtensionCLM_fst, finiteIntervalExtension_fst, intervalAmplitudeCLM_finite]
  · simp only [intervalExtensionCLM_snd, finiteIntervalExtension_snd, intervalAmplitudeCLM_finite]

/-- Every completed input lands in its selected closed boundary space. -/
theorem intervalExtensionCLM_mem (a : PairSpace p) : intervalExtensionCLM b hp hptop a ∈ space b := by
  cases b <;> simp [space, mem_dirichletSubspace, mem_neumannSubspace,
    intervalExtensionCLM_fst, intervalExtensionCLM_snd, extensionSign]

/-- Lemma 4.3 as a continuous map into the actual Dirichlet or Neumann coefficient space. -/
def intervalExtensionToBoundary : PairSpace p →L[ℂ] space (p := p) b :=
  (intervalExtensionCLM b hp hptop).codRestrict (space b) (intervalExtensionCLM_mem b hp hptop)

@[simp] theorem intervalExtensionToBoundary_coe (a : PairSpace p) :
    (intervalExtensionToBoundary b hp hptop a : PairSpace p) = intervalExtensionCLM b hp hptop a := rfl

theorem norm_intervalExtensionToBoundary_le (a : PairSpace p) :
    ‖intervalExtensionToBoundary b hp hptop a‖ ≤ intervalExtensionBound hp hptop * ‖a‖ :=
  norm_intervalExtensionCLM_apply_le b hp hptop a

/-- Bounded complex linearity yields the analyticity asserted in Lemma 4.3. -/
theorem analyticAt_intervalExtensionToBoundary (a : PairSpace p) :
    AnalyticAt ℂ (intervalExtensionToBoundary b hp hptop) a :=
  (intervalExtensionToBoundary b hp hptop).analyticAt a

/-- The physical finite-input Fourier formulas uniquely determine the continuous extension. -/
theorem intervalExtensionCLM_unique (F : PairSpace p →L[ℂ] PairSpace p)
    (hF : ∀ a, F (finitePairCoeffs a) = finiteIntervalExtension b hp a) :
    F = intervalExtensionCLM b hp hptop := by
  have he : (F : PairSpace p → PairSpace p) = intervalExtensionCLM b hp hptop := by
    apply (denseRange_finitePairCoeffs hptop).equalizer F.continuous (intervalExtensionCLM b hp hptop).continuous
    funext a
    exact (hF a).trans (intervalExtensionCLM_finite b hp hptop a).symm
  exact ContinuousLinearMap.ext (congrFun he)

/-- At exponent two, the new map is exactly the preceding Parseval completion. -/
theorem intervalExtensionCLM_two : intervalExtensionCLM b (p := 2) (by norm_num) (by simp) =
    hilbertIntervalExtension b :=
  hilbertIntervalExtension_unique b _ (intervalExtensionCLM_finite b (by norm_num) (by simp))

/-- Both physical component integrals agree with the completed extension on finite polynomials. -/
theorem intervalExtensionCLM_finite_integrals (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    (periodTwoCoefficient (fun x => (intervalExtension b (periodOnePair a) x).1) n,
      periodTwoCoefficient (fun x => (intervalExtension b (periodOnePair a) x).2) n) =
    ((intervalExtensionCLM b hp hptop (finitePairCoeffs a)).1 n,
      (intervalExtensionCLM b hp hptop (finitePairCoeffs a)).2 n) := by
  rw [intervalExtensionCLM_finite, finiteIntervalExtension_coefficient_fst b hp,
    finiteIntervalExtension_coefficient_snd b hp]

/-- Even boundary amplitudes have the exact normalized reflection formula. -/
theorem intervalAmplitudeCLM_even (a : PairSpace p) (n : ℤ) :
    intervalAmplitudeCLM b hp hptop a (2*n) = (a.2 n + extensionSign b * a.1 (-n)) / 2 := by
  change halfIntervalCoeffs hp hptop a.2 (2*n) +
    extensionSign b * halfIntervalCoeffs hp hptop a.1 (-(2*n)) = _
  rw [show -(2*n) = 2*(-n) by ring, halfIntervalCoeffs_even, halfIntervalCoeffs_even]
  ring

/-- Odd amplitudes combine the two bounded shifted transforms with the reflected index. -/
theorem intervalAmplitudeCLM_odd (a : PairSpace p) (n : ℤ) :
    intervalAmplitudeCLM b hp hptop a (2*n+1) = (I/2 : ℂ) *
      (shiftedHilbertTransform hp hptop a.2 n +
        extensionSign b * shiftedHilbertTransform hp hptop a.1 (-n-1)) := by
  change halfIntervalCoeffs hp hptop a.2 (2*n+1) +
    extensionSign b * halfIntervalCoeffs hp hptop a.1 (-(2*n+1)) = _
  rw [show -(2*n+1) = 2*(-n-1)+1 by ring, halfIntervalCoeffs_odd, halfIntervalCoeffs_odd]
  ring

end NLS.ZakharovShabat.BoundaryCondition
