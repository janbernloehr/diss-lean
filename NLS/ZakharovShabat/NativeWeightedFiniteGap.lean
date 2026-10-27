import NLS.Fourier.PeriodicFourierLebesgueSpace
import NLS.ZakharovShabat.SourceWeightedFiniteGapDensity
import NLS.ZakharovShabat.SourceFiniteGapAnalyticRealization

/-! # Finite-gap approximation in original weighted distribution spaces

The exact Fourier isometry transfers actual spectral finite-gap density to
period-one distributions with the original finite component-sum norm.
Approximants have analytic periodic representatives with every coefficient
unchanged. Scaled spectral weights recover every nonnegative Sobolev order.
-/
noncomputable section
set_option autoImplicit false
open Set Metric NLS.Fourier SmoothPeriodicTest
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat.NativeWeightedPeriodic
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original period-one distribution pairs with their weighted component-sum norm. -/
abbrev Space (w : SpectralWeight) (p : ℝ≥0∞) := WithLp p
  (PeriodicFourierLebesgue 1 (sourceFrequencyWeight w) p ×
   PeriodicFourierLebesgue 1 (sourceFrequencyWeight w) p)

theorem sourceFrequencyWeight_hasTemperedInverse (w : SpectralWeight) :
    (sourceFrequencyWeight w).HasTemperedInverse := by
  refine ⟨0, 1, by norm_num, fun n => ?_⟩
  simpa only [sourceFrequencyWeight, pow_zero, mul_one, div_one] using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (w.one_le (2*n)))

/-- The exact original Fourier coefficients, before any normalization of the weight. -/
def coefficients (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Space w p ≃ₗᵢ[ℂ] WeightedCoeffPair (sourceFrequencyWeight w) p :=
  (PeriodicFourierLebesgue.coefficientsIsometry (L := 1) _ p (sourceFrequencyWeight_hasTemperedInverse w)).withLpProdCongr p
    (PeriodicFourierLebesgue.coefficientsIsometry (L := 1) _ p (sourceFrequencyWeight_hasTemperedInverse w))

@[simp] theorem coefficients_fst (w : SpectralWeight) (φ : Space w p) (n : ℤ) :
    (coefficients w p φ).fst.val n = φ.fst.val (mode (-n)) := rfl

@[simp] theorem coefficients_snd (w : SpectralWeight) (φ : Space w p) (n : ℤ) :
    (coefficients w p φ).snd.val n = φ.snd.val (mode (-n)) := rfl

/-- The Fourier isometry, regarded as an equivalence of real normed spaces. -/
def coefficientsReal (w : SpectralWeight) :
    Space w p ≃L[ℝ] WeightedCoeffPair (sourceFrequencyWeight w) p where
  toLinearEquiv := (coefficients w p).toLinearEquiv.restrictScalars ℝ
  continuous_toFun := (coefficients w p).continuous
  continuous_invFun := (coefficients w p).symm.continuous

/-- Real type is the literal conjugate-reflection relation on the original test action. -/
def realSpace (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (Space w p) where
  carrier := {φ | ∀ n : ℤ, φ.snd.val (mode (-n)) = conj (φ.fst.val (mode n))}
  zero_mem' := by
    intro n
    change (0 : ℂ) = conj 0
    simp
  add_mem' := by
    intro φ ψ hφ hψ n
    change φ.snd.val (mode (-n)) + ψ.snd.val (mode (-n)) =
      conj (φ.fst.val (mode n) + ψ.fst.val (mode n))
    rw [map_add, hφ n, hψ n]
  smul_mem' := by
    intro r φ hφ n
    change (r : ℂ) * φ.snd.val (mode (-n)) = conj ((r : ℂ) * φ.fst.val (mode n))
    rw [map_mul, Complex.conj_ofReal, hφ n]

/-- Real type retains the literal signs in the original smooth-test action. -/
theorem mem_realSpace_iff (w : SpectralWeight) (φ : Space w p) :
    φ ∈ realSpace w p ↔ ∀ n : ℤ,
      φ.snd.val (mode (-n)) = conj (φ.fst.val (mode n)) := Iff.rfl

private theorem real_coefficients_iff (w : SpectralWeight) (φ : Space w p) :
    coefficients w p φ ∈ weightedRealSourceSubmodule (p := p) w ↔
      ∀ n : ℤ, φ.snd.val (mode (-n)) = conj (φ.fst.val (mode n)) := by
  rw [mem_weightedRealSourceSubmodule_iff]
  simp only [coefficients_snd, coefficients_fst, neg_neg]

/-- The full real distribution space and weighted real coefficients are isometric. -/
def realCoefficientsIsometry (w : SpectralWeight) :
    realSpace w p ≃ₗᵢ[ℝ] weightedRealSourceSubmodule (p := p) w where
  toFun φ := ⟨coefficients w p φ.val, (real_coefficients_iff w φ.val).mpr φ.property⟩
  invFun a := ⟨(coefficients w p).symm a.val, by
    apply (real_coefficients_iff w _).mp
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact a.property⟩
  left_inv φ := by apply Subtype.ext; exact (coefficients w p).symm_apply_apply φ.val
  right_inv a := by apply Subtype.ext; exact (coefficients w p).apply_symm_apply a.val
  map_add' φ ψ := by apply Subtype.ext; exact (coefficients w p).map_add φ.val ψ.val
  map_smul' r φ := by apply Subtype.ext; exact (coefficientsReal w).map_smul r φ.val
  norm_map' φ := (coefficients w p).norm_map φ.val

instance (w : SpectralWeight) : CompleteSpace (realSpace w p) :=
  (realCoefficientsIsometry w).toIsometryEquiv.completeSpace

/-- The same isometry as a continuous linear equivalence. -/
def realCoefficientsEquiv (w : SpectralWeight) :
    realSpace w p ≃L[ℝ] weightedRealSourceSubmodule (p := p) w :=
  (realCoefficientsIsometry w).toContinuousLinearEquiv

@[simp] theorem norm_realCoefficientsEquiv (w : SpectralWeight) (φ : realSpace w p) :
    ‖realCoefficientsEquiv w φ‖ = ‖φ‖ := (realCoefficientsIsometry w).norm_map φ

/-- The original potential parameter, obtained without altering any raw coefficient. -/
def source (w : SpectralWeight) (φ : realSpace w p) : realTypeSourceSubmodule p :=
  originalWeightedRealSource w (realCoefficientsEquiv w φ)

@[simp] theorem source_fst (w : SpectralWeight) (φ : realSpace w p) (n : ℤ) :
    (source w φ).val.fst n = φ.val.fst.val (mode (-n)) :=
  originalWeightedRealSource_fst w _ n

@[simp] theorem source_snd (w : SpectralWeight) (φ : realSpace w p) (n : ℤ) :
    (source w φ).val.snd n = φ.val.snd.val (mode (-n)) :=
  originalWeightedRealSource_snd w _ n

/-- Finite-gap means finitely many open canonical spectral gaps of the same potential. -/
def finiteGapLocus (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) : Set (realSpace w p) :=
  {φ | source w φ ∈ sourceFiniteGapLocus hp hp1}

/-- The spectral definition is exactly vanishing beyond one positive signed-index cutoff. -/
theorem mem_finiteGapLocus_iff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : realSpace w p) :
    φ ∈ finiteGapLocus hp hp1 w ↔ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℤ, N < n.natAbs →
      canonicalPeriodicGap hp hp1 (periodOnePotential (source w φ).val)
        (periodOnePotential_mem (source w φ).val) n = 0 := by
  change {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential (source w φ).val)
    (periodOnePotential_mem (source w φ).val) n ≠ 0}.Finite ↔ _
  constructor
  · intro hf
    obtain ⟨N, hN⟩ := (hf.image Int.natAbs).bddAbove
    refine ⟨max N 1, le_max_right _ _, fun n hn => ?_⟩
    by_contra hgap
    have hb := hN (Set.mem_image_of_mem Int.natAbs hgap)
    omega
  · rintro ⟨N, _, h⟩
    apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
    intro n hn
    have hb : n.natAbs ≤ N := le_of_not_gt (fun hh => hn (h n hh))
    simp only [Set.mem_Icc]
    omega

/-- Approximation in the exact original weighted distribution norm. -/
theorem exists_finiteGap_norm_sub_lt (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : realSpace w p) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ ∈ finiteGapLocus hp hp1 w, ‖ψ - φ‖ < ε := by
  obtain ⟨b, hb, hclose⟩ := exists_weightedRealSource_finiteGap_norm_sub_lt hp hp1 w
    (realCoefficientsEquiv w φ) ε hε
  refine ⟨(realCoefficientsEquiv w).symm b, ?_, ?_⟩
  · simpa only [finiteGapLocus, mem_ofPred_eq, source, ContinuousLinearEquiv.apply_symm_apply] using hb
  · rw [← norm_realCoefficientsEquiv w, map_sub, ContinuousLinearEquiv.apply_symm_apply]
    exact hclose

/-- Spectral finite-gap distributions are dense in the full original weighted real space. -/
theorem dense_finiteGapLocus (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) :
    Dense (finiteGapLocus hp hp1 w) := by
  apply Metric.dense_iff.mpr
  intro φ ε hε
  obtain ⟨ψ, hψ, hclose⟩ := exists_finiteGap_norm_sub_lt hp hp1 w φ ε hε
  exact ⟨ψ, by simpa only [mem_ball, dist_eq_norm] using hclose, hψ⟩

/-- Every approximant has analytic periodic representatives with its actual Fourier coefficients. -/
theorem exists_analytic_representative (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : realSpace w p) (hf : φ ∈ finiteGapLocus hp hp1 w) :
    ∃ u v : ℝ → ℂ, AnalyticOnNhd ℝ u univ ∧ AnalyticOnNhd ℝ v univ ∧
      Function.Periodic u 1 ∧ Function.Periodic v 1 ∧
      ∀ n : ℤ, periodOneCoefficient u n = φ.val.fst.val (mode (-n)) ∧
        periodOneCoefficient v n = φ.val.snd.val (mode (-n)) := by
  simpa only [source_fst, source_snd] using
    sourceFiniteGap_exists_analytic_representative hp hp1 (source w φ) hf

/-- Half scaling compensates exactly for the doubled spectral frequencies. -/
def sobolevWeight (s : ℝ) (hs : 0 ≤ s) : SpectralWeight :=
  SpectralWeight.scaledSobolev (1/2) s (by norm_num) hs

@[simp] theorem sourceFrequencyWeight_sobolevWeight (s : ℝ) (hs : 0 ≤ s) :
    sourceFrequencyWeight (sobolevWeight s hs) = Weight.sobolev s := by
  unfold sourceFrequencyWeight Weight.sobolev
  congr 1
  funext n
  simp [sobolevWeight, SpectralWeight.scaledSobolev_apply,
    abs_mul]

/-- Density at every nonnegative real Sobolev order, including fractional orders. -/
theorem dense_sobolev_finiteGapLocus (hp : p ≠ ⊤) (hp1 : 1 < p) (s : ℝ) (hs : 0 ≤ s) :
    Dense (finiteGapLocus hp hp1 (sobolevWeight s hs)) :=
  dense_finiteGapLocus hp hp1 _

end NLS.ZakharovShabat.NativeWeightedPeriodic
