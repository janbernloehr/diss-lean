import NLS.ZakharovShabat.SourceNormalizedActionCircleExpansion
import NLS.ZakharovShabat.SourceStandardRootProductFactors

/-!
# Bounds for the complex normalized-action contour correction

On a circle separated from a sufficiently small complex gap, the
selected standard root stays close to its zero-gap value. This gives
quantitative lower bounds for every denominator in the correction
kernel and permits a direct contour estimate.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The selected standard root differs from its zero-gap value by
at most the squared-gap size divided by the spectral distance. -/
theorem norm_normalizedStandardRoot_sub_zeroGap_le
    (τ q z : ℂ) (hτ : τ ≠ z) :
    ‖normalizedStandardRoot τ q z - (τ-z)‖ ≤
      ‖q‖/(4*‖τ-z‖) := by
  have hd : τ-z ≠ 0 := sub_ne_zero.mpr hτ
  have hdpos : 0 < ‖τ-z‖ := norm_pos_iff.mpr hd
  have heq : normalizedStandardRoot τ q z - (τ-z) =
      (τ-z)*(Complex.sqrt (1-q/(4*(τ-z)^2))-1) := by
    unfold normalizedStandardRoot
    ring
  rw [heq, norm_mul]
  calc
    ‖τ-z‖ * ‖Complex.sqrt (1-q/(4*(τ-z)^2))-1‖ ≤
        ‖τ-z‖ * ‖q/(4*(τ-z)^2)‖ :=
      mul_le_mul_of_nonneg_left
        (norm_sqrt_one_sub_sub_one_le _) hdpos.le
    _ = ‖q‖/(4*‖τ-z‖) := by
      rw [norm_div, norm_mul, norm_pow]
      norm_num only [Complex.norm_ofNat]
      field_simp

/-- A squared gap no larger than the squared spectral distance keeps
the selected root and the rationalizing denominator separated from
zero by fixed fractions of that distance. -/
theorem normalizedStandardRoot_denominator_lower_bounds
    (τ q z : ℂ) (hτ : τ ≠ z)
    (hq : ‖q‖ ≤ ‖τ-z‖^2) :
    ‖τ-z‖/2 ≤ ‖normalizedStandardRoot τ q z‖ ∧
      ‖τ-z‖ ≤ ‖τ-z+normalizedStandardRoot τ q z‖ := by
  let d := τ-z
  let w := normalizedStandardRoot τ q z
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hτ)
  have hdev : ‖w-d‖ ≤ ‖d‖/4 := by
    have hbase := norm_normalizedStandardRoot_sub_zeroGap_le τ q z hτ
    change ‖w-d‖ ≤ ‖q‖/(4*‖d‖) at hbase
    apply hbase.trans
    apply (div_le_iff₀ (by positivity : 0 < 4*‖d‖)).mpr
    nlinarith
  have hwd : ‖d‖ ≤ ‖w‖+‖w-d‖ := by
    have heq : d = w-(w-d) := by ring
    calc
      ‖d‖ = ‖w-(w-d)‖ := congrArg norm heq
      _ ≤ ‖w‖+‖w-d‖ := norm_sub_le _ _
  have hplus : 2*‖d‖ ≤ ‖d+w‖+‖w-d‖ := by
    have heq : 2*d = (d+w)-(w-d) := by ring
    have h := norm_sub_le (d+w) (w-d)
    rw [← heq, norm_mul] at h
    norm_num at h
    exact h
  constructor
  · change ‖d‖/2 ≤ ‖w‖
    linarith
  · change ‖d‖ ≤ ‖d+w‖
    linarith

/-- Splitting the first rational term removes its numerator, so
lower bounds on the three spectral denominators suffice for norm
estimates. -/
theorem normalizedActionCircleKernelCorrection_eq_four_terms
    (τ q B z : ℂ) (hτ : τ ≠ z)
    (hw : normalizedStandardRoot τ q z ≠ 0)
    (hplus : τ-z+normalizedStandardRoot τ q z ≠ 0) :
    normalizedActionCircleKernelCorrection τ q B z =
      1/(16*normalizedStandardRoot τ q z *
        (τ-z+normalizedStandardRoot τ q z)^2) +
      1/(32*(τ-z)*(τ-z+normalizedStandardRoot τ q z)^2) +
      B/(2*normalizedStandardRoot τ q z *
        (τ-z+normalizedStandardRoot τ q z)) +
      B^2/normalizedStandardRoot τ q z := by
  have hd : τ-z ≠ 0 := sub_ne_zero.mpr hτ
  unfold normalizedActionCircleKernelCorrection
  dsimp only
  field_simp
  ring

/-- A direct pointwise norm bound for the complex contour correction. -/
theorem norm_normalizedActionCircleKernelCorrection_le
    (τ q B z : ℂ) (hτ : τ ≠ z)
    (hw : normalizedStandardRoot τ q z ≠ 0)
    (hplus : τ-z+normalizedStandardRoot τ q z ≠ 0) :
    ‖normalizedActionCircleKernelCorrection τ q B z‖ ≤
      1/(16*‖normalizedStandardRoot τ q z‖ *
        ‖τ-z+normalizedStandardRoot τ q z‖^2) +
      1/(32*‖τ-z‖*‖τ-z+normalizedStandardRoot τ q z‖^2) +
      ‖B‖/(2*‖normalizedStandardRoot τ q z‖ *
        ‖τ-z+normalizedStandardRoot τ q z‖) +
      ‖B‖^2/‖normalizedStandardRoot τ q z‖ := by
  rw [normalizedActionCircleKernelCorrection_eq_four_terms τ q B z hτ hw hplus]
  calc
    _ ≤ ‖1/(16*normalizedStandardRoot τ q z *
        (τ-z+normalizedStandardRoot τ q z)^2) +
        1/(32*(τ-z)*(τ-z+normalizedStandardRoot τ q z)^2) +
        B/(2*normalizedStandardRoot τ q z *
          (τ-z+normalizedStandardRoot τ q z))‖ +
        ‖B^2/normalizedStandardRoot τ q z‖ := norm_add_le _ _
    _ ≤ ‖1/(16*normalizedStandardRoot τ q z *
        (τ-z+normalizedStandardRoot τ q z)^2) +
        1/(32*(τ-z)*(τ-z+normalizedStandardRoot τ q z)^2)‖ +
        ‖B/(2*normalizedStandardRoot τ q z *
          (τ-z+normalizedStandardRoot τ q z))‖ +
        ‖B^2/normalizedStandardRoot τ q z‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖1/(16*normalizedStandardRoot τ q z *
        (τ-z+normalizedStandardRoot τ q z)^2)‖ +
        ‖1/(32*(τ-z)*(τ-z+normalizedStandardRoot τ q z)^2)‖ +
        ‖B/(2*normalizedStandardRoot τ q z *
          (τ-z+normalizedStandardRoot τ q z))‖ +
        ‖B^2/normalizedStandardRoot τ q z‖ := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by
      simp only [norm_div, norm_mul, norm_pow, norm_one]
      norm_num only [Complex.norm_ofNat]

/-- When the squared gap is smaller than the squared distance to the
contour, the correction is bounded by a cubic spectral pole and two
terms controlled by the critical-gap coefficient. -/
theorem norm_normalizedActionCircleKernelCorrection_le_of_small_gap
    (τ q B z : ℂ) (hτ : τ ≠ z)
    (hq : ‖q‖ ≤ ‖τ-z‖^2) :
    ‖normalizedActionCircleKernelCorrection τ q B z‖ ≤
      2/‖τ-z‖^3 + ‖B‖/‖τ-z‖^2 +
        2*‖B‖^2/‖τ-z‖ := by
  let D := ‖τ-z‖
  let W := ‖normalizedStandardRoot τ q z‖
  let S := ‖τ-z+normalizedStandardRoot τ q z‖
  have hD : 0 < D := norm_pos_iff.mpr (sub_ne_zero.mpr hτ)
  obtain ⟨hW,hS⟩ := normalizedStandardRoot_denominator_lower_bounds τ q z hτ hq
  have hWpos : 0 < W := by dsimp [W,D] at *; linarith
  have hSpos : 0 < S := hD.trans_le hS
  have hwne : normalizedStandardRoot τ q z ≠ 0 := norm_pos_iff.mp hWpos
  have hsne : τ-z+normalizedStandardRoot τ q z ≠ 0 := norm_pos_iff.mp hSpos
  have hDle2W : D ≤ 2*W := by linarith
  have hD2leS2 : D^2 ≤ S^2 := pow_le_pow_left₀ hD.le hS 2
  have hD3 : D^3 ≤ 16*W*S^2 := by
    calc
      D^3 = D*D^2 := by ring
      _ ≤ (2*W)*S^2 := by
        gcongr
      _ ≤ 16*W*S^2 := by nlinarith [mul_nonneg (le_of_lt hWpos) (sq_nonneg S)]
  have hD3' : D^3 ≤ 32*D*S^2 := by
    have h := mul_le_mul_of_nonneg_left hD2leS2 hD.le
    nlinarith [mul_nonneg hD.le (sq_nonneg S)]
  have hD2 : D^2 ≤ 2*W*S := by
    calc
      D^2 = D*D := by ring
      _ ≤ (2*W)*S := by gcongr
      _ = 2*W*S := by ring
  have hfirst : 1/(16*W*S^2) ≤ 1/D^3 :=
    one_div_le_one_div_of_le (by positivity) hD3
  have hsecond : 1/(32*D*S^2) ≤ 1/D^3 :=
    one_div_le_one_div_of_le (by positivity) hD3'
  have hthird : ‖B‖/(2*W*S) ≤ ‖B‖/D^2 :=
    div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hD2
  have hfourth : ‖B‖^2/W ≤ 2*‖B‖^2/D := by
    apply (div_le_div_iff₀ hWpos hD).mpr
    nlinarith [mul_le_mul_of_nonneg_left hDle2W (sq_nonneg ‖B‖)]
  have hmain := norm_normalizedActionCircleKernelCorrection_le
    τ q B z hτ hwne hsne
  change ‖normalizedActionCircleKernelCorrection τ q B z‖ ≤
    1/(16*W*S^2) + 1/(32*D*S^2) + ‖B‖/(2*W*S) + ‖B‖^2/W at hmain
  change ‖normalizedActionCircleKernelCorrection τ q B z‖ ≤
    2/D^3 + ‖B‖/D^2 + 2*‖B‖^2/D
  calc
    _ ≤ 1/D^3 + 1/D^3 + ‖B‖/D^2 + 2*‖B‖^2/D := by linarith
    _ = _ := by ring

/-- A contour separated by `a` from the midpoint has an explicit
correction bound whenever the squared gap is at most `a²` and the
critical-gap coefficient is bounded by `M`. -/
theorem norm_normalizedActionCircleKernelCorrection_le_of_separation
    (τ q B z : ℂ) (a M : ℝ) (ha : 0 < a)
    (hsep : a ≤ ‖τ-z‖) (hq : ‖q‖ ≤ a^2)
    (hB : ‖B‖ ≤ M) :
    ‖normalizedActionCircleKernelCorrection τ q B z‖ ≤
      2/a^3 + M/a^2 + 2*M^2/a := by
  have hτ : τ ≠ z := sub_ne_zero.mp (norm_pos_iff.mp (ha.trans_le hsep))
  have hq' : ‖q‖ ≤ ‖τ-z‖^2 :=
    hq.trans (pow_le_pow_left₀ ha.le hsep 2)
  have hM : 0 ≤ M := (norm_nonneg B).trans hB
  have hmain := norm_normalizedActionCircleKernelCorrection_le_of_small_gap
    τ q B z hτ hq'
  calc
    ‖normalizedActionCircleKernelCorrection τ q B z‖ ≤
        2/‖τ-z‖^3 + ‖B‖/‖τ-z‖^2 + 2*‖B‖^2/‖τ-z‖ := hmain
    _ ≤ 2/a^3 + M/a^2 + 2*M^2/a := by
      gcongr

/-- The normalized contour quotient differs from its midpoint term
by at most the squared-gap size times an explicit spectral bound.
All hypotheses are stable under small complex source perturbations. -/
theorem norm_normalizedActionCircleQuotient_sub_midpoint_le
    (τ q B c : ℂ) (R : ℝ) (E : ℂ → ℂ)
    (hR : 0 < R) (hτ : τ ∈ ball c R)
    (hE : AnalyticOnNhd ℂ E (closedBall c R))
    (hroot : ∀ z ∈ sphere c R,
      AnalyticAt ℂ (normalizedStandardRoot τ q) z)
    (hden : ∀ z ∈ sphere c R,
      τ ≠ z ∧ normalizedStandardRoot τ q z ≠ 0 ∧
        τ-z+normalizedStandardRoot τ q z ≠ 0)
    (a M L : ℝ) (ha : 0 < a)
    (hsep : ∀ z ∈ sphere c R, a ≤ ‖τ-z‖)
    (hq : ‖q‖ ≤ a^2) (hB : ‖B‖ ≤ M)
    (hEbound : ∀ z ∈ sphere c R, ‖E z‖ ≤ L) :
    ‖normalizedActionCircleQuotient τ q B c R E - I*E τ/4‖ ≤
      2*R*‖q‖ * (2/a^3 + M/a^2 + 2*M^2/a) * L := by
  let K : ℝ := 2/a^3 + M/a^2 + 2*M^2/a
  have hM : 0 ≤ M := (norm_nonneg B).trans hB
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint : ∀ z ∈ sphere c R,
      ‖normalizedActionCircleKernelCorrection τ q B z * E z‖ ≤ K*L := by
    intro z hz
    rw [norm_mul]
    exact mul_le_mul
      (norm_normalizedActionCircleKernelCorrection_le_of_separation
        τ q B z a M ha (hsep z hz) hq hB)
      (hEbound z hz) (norm_nonneg _) hK
  have hInt := circleIntegral.norm_integral_le_of_norm_le_const
    hR.le hpoint
  have hexp := normalizedActionCircleQuotient_eq_midpoint_sub_correction_of_analyticRoot
    τ q B c R E hR hτ hE hroot hden
  rw [hexp]
  have hpi : ‖(Real.pi:ℂ)⁻¹‖ = Real.pi⁻¹ := by
    simp [Real.pi_pos.le]
  calc
    ‖I*E τ/4 - q*(Real.pi:ℂ)⁻¹ *
        (∮ z in C(c,R), normalizedActionCircleKernelCorrection τ q B z * E z) -
        I*E τ/4‖ =
      ‖q‖ * Real.pi⁻¹ *
        ‖∮ z in C(c,R), normalizedActionCircleKernelCorrection τ q B z * E z‖ := by
      have heq : I*E τ/4 - q*(Real.pi:ℂ)⁻¹ *
          (∮ z in C(c,R), normalizedActionCircleKernelCorrection τ q B z * E z) -
          I*E τ/4 =
        -(q*(Real.pi:ℂ)⁻¹ *
          (∮ z in C(c,R), normalizedActionCircleKernelCorrection τ q B z * E z)) := by ring
      rw [heq, norm_neg, norm_mul, norm_mul, hpi]
    _ ≤ ‖q‖ * Real.pi⁻¹ * (2*Real.pi*R*(K*L)) := by
      gcongr
    _ = 2*R*‖q‖*K*L := by
      have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp

/-- The fixed-index complex normalized action inherits the contour
correction estimate on the neighborhood carrying its expansion. The
remaining uniform-index task is to provide common separation and
deleted-factor bounds for all distant circles. -/
theorem exists_local_sourceNormalizedActionComplexExtension_correction_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        ∀ ψ ∈ U, ∀ a M L : ℝ, 0 < a →
          (∀ z ∈ sphere c R,
            a ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖) →
          ‖(sourcePeriodicGapDisplacement hp hp1 ψ n)^2‖ ≤ a^2 →
          ‖canonicalCriticalGapQuotient hp hp1
            (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤ M →
          (∀ z ∈ sphere c R,
            ‖sourceCriticalRootRatioExtension hp hp1 n ψ z‖ ≤ L) →
          ‖sourceNormalizedActionComplexExtension hp hp1 n ψ -
            I*sourceCriticalRootRatioExtension hp hp1 n ψ
              (sourceStandardRootMidpoint hp hp1 ψ n)/4‖ ≤
            2*R*‖(sourcePeriodicGapDisplacement hp hp1 ψ n)^2‖ *
              (2/a^3 + M/a^2 + 2*M^2/a) * L := by
  obtain ⟨U,hUopen,hφU,c,R,hR,hexp⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_circleExpansion
      hp hp1 φ hφ n
  refine ⟨U,hUopen,hφU,c,R,hR,?_⟩
  intro ψ hψ a M L ha hsep hq hB hEbound
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let q := (sourcePeriodicGapDisplacement hp hp1 ψ n)^2
  let B := canonicalCriticalGapQuotient hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let E := sourceCriticalRootRatioExtension hp hp1 n ψ
  let K : ℝ := 2/a^3 + M/a^2 + 2*M^2/a
  have hM : 0 ≤ M := (norm_nonneg B).trans hB
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint : ∀ z ∈ sphere c R,
      ‖normalizedActionCircleKernelCorrection τ q B z * E z‖ ≤ K*L := by
    intro z hz
    rw [norm_mul]
    exact mul_le_mul
      (norm_normalizedActionCircleKernelCorrection_le_of_separation
        τ q B z a M ha (hsep z hz) hq hB)
      (hEbound z hz) (norm_nonneg _) hK
  have hInt := circleIntegral.norm_integral_le_of_norm_le_const
    hR.le hpoint
  rw [hexp ψ hψ]
  change ‖I*E τ/4 - q*(Real.pi:ℂ)⁻¹ *
      (∮ z in C(c,R), normalizedActionCircleKernelCorrection τ q B z * E z) -
      I*E τ/4‖ ≤ 2*R*‖q‖*K*L
  have hpi : ‖(Real.pi:ℂ)⁻¹‖ = Real.pi⁻¹ := by simp [Real.pi_pos.le]
  calc
    _ = ‖q‖ * Real.pi⁻¹ *
        ‖∮ z in C(c,R), normalizedActionCircleKernelCorrection τ q B z * E z‖ := by
      have heq : I*E τ/4 - q*(Real.pi:ℂ)⁻¹ *
          (∮ z in C(c,R), normalizedActionCircleKernelCorrection τ q B z * E z) -
          I*E τ/4 =
        -(q*(Real.pi:ℂ)⁻¹ *
          (∮ z in C(c,R), normalizedActionCircleKernelCorrection τ q B z * E z)) := by ring
      rw [heq, norm_neg, norm_mul, norm_mul, hpi]
    _ ≤ ‖q‖ * Real.pi⁻¹ * (2*Real.pi*R*(K*L)) := by gcongr
    _ = 2*R*‖q‖*K*L := by
      have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp

end NLS.ZakharovShabat
