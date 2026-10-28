import NLS.ZakharovShabat.ResonantCubicBackground

/-! # Actual original coefficient errors and strip suprema

These statements concern original period-two coefficients, actual whole-strip
suprema and infinite signed sums. The final source inequality still requires
the asymptotics of the actual counted-root gap; it is not resolved here.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceCubicCoefficientErrorFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The fixed two-mode background in unit-weight coordinates. -/
def sourceCubicBackgroundProfile (n : ℤ) := twoModeResonantPotential (p := 4) SpectralWeight.one n 1
/-- The fixed resonant profile added with cubic amplitude. -/
def sourceCubicResonantProfile (n : ℤ) := singleResonantPotential (p := 4) SpectralWeight.one n
  (sourceCubicTailScale n) (sourceCubicTailScale n)

/-- The actual full-strip supremum of the selected cubic perturbation. -/
def sourceCubicPerturbationSup (n : ℤ) (s : ℝ) (m : ℤ) (positive : Bool) : ℝ :=
  if positive then resonantCubicPerturbationSup (by simp) SpectralWeight.one (sourceCubicBackgroundProfile n) (sourceCubicResonantProfile n) m (s : ℂ) 1 0
  else resonantCubicPerturbationSup (by simp) SpectralWeight.one (sourceCubicBackgroundProfile n) (sourceCubicResonantProfile n) m (s : ℂ) 0 1

/-- The full-strip error after subtracting the family's own cubic term. -/
def sourceCubicHigherErrorSup (n : ℤ) (s : ℝ) (m : ℤ) (positive : Bool) : ℝ :=
  resonantCubicErrorSup (by simp) SpectralWeight.one (weightedCubicTailFamily n s) m positive

/-- The sum of the higher Neumann error and cubic perturbation suprema. -/
def sourceCubicCombinedError (n : ℤ) (s : ℝ) (m : ℤ) (positive : Bool) : ℝ := sourceCubicHigherErrorSup n s m positive+sourceCubicPerturbationSup n s m positive

/-- The actual selected coefficient with its leading Fourier term subtracted. -/
def sourceCubicRemainderFunction (n : ℤ) (s : ℝ) (m : ℤ) (positive : Bool) (z : ℂ) : ℂ :=
  if positive then weightedResonantBPlusExtension (by simp) SpectralWeight.one
    (weightedCubicTailFamily n s) m z-(weightedCubicTailFamily n s).snd.val (2*m)
  else weightedResonantBMinusExtension (by simp) SpectralWeight.one
    (weightedCubicTailFamily n s) m z-(weightedCubicTailFamily n s).fst.val (-(2*m))

/-- The selected original-source remainder supremum on the whole closed strip. -/
def sourceCubicRemainderSup (n : ℤ) (s : ℝ) (m : ℤ) (positive : Bool) : ℝ :=
  if positive then sourceResonantBPlusSup (by simp) SpectralWeight.one (sourceCubicTailFamily n s) m
  else sourceResonantBMinusSup (by simp) SpectralWeight.one (sourceCubicTailFamily n s) m

/-- The original supremum equals the weighted full-strip supremum of the actual remainder. -/
theorem sourceCubicRemainderSup_eq (n : ℤ) (s : ℝ) (m : ℤ) (positive : Bool) :
    sourceCubicRemainderSup n s m positive = weightedStripSup SpectralWeight.one m (sourceCubicRemainderFunction n s m positive) := by
  cases positive
  · unfold sourceCubicRemainderSup sourceResonantBMinusSup sourceCubicRemainderFunction
    simp only [Bool.false_eq_true,if_false]
    have hf := unitWeightedPairEquiv_fst (sourceCubicTailFamily n s) (-(2*m))
    rw [unitWeightedPairEquiv_sourceCubicTailFamily] at hf
    simp only [sourceResonantBMinusFunction,sourceCorrectionEntryFunction,
      unitWeightedPairEquiv_sourceCubicTailFamily,hf]
    rfl
  · unfold sourceCubicRemainderSup sourceResonantBPlusSup sourceCubicRemainderFunction
    simp only [if_true]
    have hf := unitWeightedPairEquiv_snd (sourceCubicTailFamily n s) (2*m)
    rw [unitWeightedPairEquiv_sourceCubicTailFamily] at hf
    simp only [sourceResonantBPlusFunction,sourceCorrectionEntryFunction,
      unitWeightedPairEquiv_sourceCubicTailFamily,hf]
    rfl

/-- An explicit smallness condition ensuring half-contraction on every strip. -/
def SourceCubicSmall (n : ℤ) (s : ℝ) : Prop :=
  2*weightedDoubleConstant (p := 4) (by simp)*‖weightedCubicTailFamily n s‖^2 ≤ 1/2

/-- The higher error supremum is nonnegative and controls every strip value. -/
theorem sourceCubicHigherErrorSup_bounds (n : ℤ) (s : ℝ) (m : ℤ) (positive : Bool) (hs : SourceCubicSmall n s) :
    0 ≤ sourceCubicHigherErrorSup n s m positive ∧ ∀ z ∈ resonantStrip m,
      ‖resonantCubicErrorFunction (by simp) SpectralWeight.one (weightedCubicTailFamily n s) m positive z‖ ≤
        sourceCubicHigherErrorSup n s m positive := by
  have h := (resonantCubicErrorSup_bounds (p := 4) (by simp) (by norm_num)
    SpectralWeight.one (weightedCubicTailFamily n s) 0 m (by omega) positive
    (2*weightedDoubleConstant (p := 4) (by simp)*‖weightedCubicTailFamily n s‖^2)
    (fun z hz => ⟨(resonantCubic_square_bound (by simp) SpectralWeight.one _ m z hz).trans hs,
      resonantCubic_square_bound (by simp) SpectralWeight.one _ m z hz⟩)).2
  exact ⟨h.1,by simpa only [SpectralWeight.one_apply,one_mul,sourceCubicHigherErrorSup] using h.2.2⟩

/-- The cubic perturbation supremum is nonnegative and controls every strip value. -/
theorem sourceCubicPerturbationSup_bounds (n : ℤ) (s : ℝ) (m : ℤ) (positive : Bool)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ sourceCubicPerturbationSup n s m positive ∧ ∀ z ∈ resonantStrip m,
      ‖resonantCubicTermFunction (by simp) SpectralWeight.one (weightedCubicTailFamily n s) m positive z -
        resonantCubicTermFunction (by simp) SpectralWeight.one ((s : ℂ) • sourceCubicBackgroundProfile n) m positive z‖ ≤
        sourceCubicPerturbationSup n s m positive := by
  have hnorm : ‖(s : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real,Real.norm_of_nonneg hs] using hs1
  have hf : weightedCubicTailFamily n s = (s : ℂ) • sourceCubicBackgroundProfile n+(s : ℂ)^3 • sourceCubicResonantProfile n := by
    simp only [weightedCubicTailFamily,sourceCubicBackgroundProfile,sourceCubicResonantProfile,Complex.ofReal_pow]
  rw [hf]
  cases positive
  · exact ⟨(resonantCubicPerturbationSup_bounds (by simp) SpectralWeight.one (sourceCubicBackgroundProfile n) (sourceCubicResonantProfile n) m (s : ℂ) hnorm 0 1).1,
      fun z hz => by simpa only [resonantCubicTermFunction,Bool.false_eq_true,if_false,sourceCubicPerturbationSup,
        SpectralWeight.one_apply,one_mul] using
          resonantCubicPerturbationSup_pointwise (by simp) SpectralWeight.one (sourceCubicBackgroundProfile n) (sourceCubicResonantProfile n) m (s : ℂ) z hnorm hz 0 1⟩
  · exact ⟨(resonantCubicPerturbationSup_bounds (by simp) SpectralWeight.one (sourceCubicBackgroundProfile n) (sourceCubicResonantProfile n) m (s : ℂ) hnorm 1 0).1,
      fun z hz => by simpa only [resonantCubicTermFunction,if_true,sourceCubicPerturbationSup,SpectralWeight.one_apply,one_mul] using
        resonantCubicPerturbationSup_pointwise (by simp) SpectralWeight.one (sourceCubicBackgroundProfile n) (sourceCubicResonantProfile n) m (s : ℂ) z hnorm hz 1 0⟩

/-- The exact two-mode cubic background on the signed outer tail. -/
def sourceCubicBackgroundFunction (n m : ℤ) (s : ℝ) (z : ℂ) : ℂ := if m=n then (s : ℂ)^3/z^2 else 0
/-- The unit-amplitude full-strip cubic supremum at the positive target index. -/
def sourceCubicBackgroundScale (n : ℤ) : ℝ := 1/(Real.pi*((n : ℝ)-1/2))^2

/-- The actual remainder differs from its exact background by the combined error. -/
theorem sourceCubicCombinedError_pointwise (n m : ℤ) (hn : 0 < n) (hm : n ≤ |m|) (s : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hsmall : SourceCubicSmall n s) (positive : Bool)
    (z : ℂ) (hz : z ∈ resonantStrip m) :
    ‖sourceCubicRemainderFunction n s m positive z-sourceCubicBackgroundFunction n m s z‖ ≤ sourceCubicCombinedError n s m positive := by
  have hb := resonantCubicTermFunction_twoMode (p := 4) (by simp) SpectralWeight.one n m hn hm (s : ℂ) z hz positive
  have he : sourceCubicRemainderFunction n s m positive z-sourceCubicBackgroundFunction n m s z =
      resonantCubicErrorFunction (by simp) SpectralWeight.one (weightedCubicTailFamily n s) m positive z +
      (resonantCubicTermFunction (by simp) SpectralWeight.one (weightedCubicTailFamily n s) m positive z -
        resonantCubicTermFunction (by simp) SpectralWeight.one ((s : ℂ) • sourceCubicBackgroundProfile n) m positive z) := by
    rw [show resonantCubicTermFunction (by simp) SpectralWeight.one ((s : ℂ) • sourceCubicBackgroundProfile n) m positive z =
      sourceCubicBackgroundFunction n m s z from hb]
    unfold resonantCubicErrorFunction sourceCubicRemainderFunction
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add ((sourceCubicHigherErrorSup_bounds n s m positive hsmall).2 z hz)
    ((sourceCubicPerturbationSup_bounds n s m positive hs hs1).2 z hz))

/-- The background has the specified full-strip supremum, which bounds every value. -/
theorem sourceCubicBackgroundFunction_bounds (n m : ℤ) (hn : 0 < n) (s : ℝ) (hs : 0 ≤ s) :
    weightedStripSup SpectralWeight.one m (sourceCubicBackgroundFunction n m s) =
      (if m=n then s^3*sourceCubicBackgroundScale n else 0) ∧
    ∀ z ∈ resonantStrip m, ‖sourceCubicBackgroundFunction n m s z‖ ≤ (if m=n then s^3*sourceCubicBackgroundScale n else 0) := by
  by_cases hm : m=n
  · subst m
    have h := resonantCubic_strip_isGreatest n hn (s : ℂ)
    have he : ‖(s : ℂ)‖^3/(Real.pi*((n : ℝ)-1/2))^2 = s^3*sourceCubicBackgroundScale n := by
      simp [sourceCubicBackgroundScale,Complex.norm_real,Real.norm_of_nonneg hs,div_eq_mul_inv]
    constructor
    · simp only [weightedStripSup,sourceCubicBackgroundFunction,if_true,SpectralWeight.one_apply,one_mul]
      rw [resonantCubic_strip_sup n hn,he]
    · intro z hz
      simpa only [sourceCubicBackgroundFunction,if_true,he] using h.2 ⟨z,hz,rfl⟩
  · have h := weightedStripSup_bounds SpectralWeight.one m (sourceCubicBackgroundFunction n m s) 0 (by
      intro z hz
      simp [sourceCubicBackgroundFunction,hm])
    exact ⟨by simpa only [if_neg hm] using le_antisymm h.2.1 h.1,
      by intro z hz; simp [sourceCubicBackgroundFunction,hm]⟩

/-- The actual original remainder supremum differs from the background supremum by at most the combined error. -/
theorem sourceCubicRemainderSup_bounds (n m : ℤ) (hn : 0 < n) (hm : n ≤ |m|) (s : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hsmall : SourceCubicSmall n s) (positive : Bool) :
    0 ≤ sourceCubicRemainderSup n s m positive ∧
    |sourceCubicRemainderSup n s m positive-(if m=n then s^3*sourceCubicBackgroundScale n else 0)| ≤ sourceCubicCombinedError n s m positive := by
  rw [sourceCubicRemainderSup_eq]
  have hb := sourceCubicBackgroundFunction_bounds n m hn s hs
  have h := unitWeightedStripSup_difference m (sourceCubicRemainderFunction n s m positive) (sourceCubicBackgroundFunction n m s)
    (sourceCubicCombinedError n s m positive) (if m=n then s^3*sourceCubicBackgroundScale n else 0) hb.2
    (sourceCubicCombinedError_pointwise n m hn hm s hs hs1 hsmall positive)
  rwa [hb.1] at h

end NLS.ZakharovShabat
