import NLS.ComplexAnalysis.HermitianFourierAssembly
import NLS.ZakharovShabat.ClassicalHermitianOperatorBound
import NLS.ZakharovShabat.ClassicalSobolevRemainderFourierDecay
import NLS.ZakharovShabat.ClassicalShiftedFreeFourierDecay

/-! # G.3 Fourier decay for the full fundamental matrix

The sequence norm uses the genuine Hermitian induced operator norm of each
actual Bochner Fourier coefficient. Both near-free and shifted-free claims
retain their common cutoffs and their different displacement hypotheses.
-/
noncomputable section
open Set MeasureTheory NLS.Fourier NLS.ComplexAnalysis NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Assemble the four coordinate observations of the two fundamental columns. -/
def hermitianObservationAssembly {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (F : (ℂ × ℂ) → ((ℂ × ℂ) →L[ℝ] ℂ) → Coeff q) : HermitianCoeff q :=
  hermitianFourierAssembly
    (F (1,0) (ContinuousLinearMap.fst ℝ ℂ ℂ))
    (F (1,0) (ContinuousLinearMap.snd ℝ ℂ ℂ))
    (F (0,1) (ContinuousLinearMap.fst ℝ ℂ ℂ))
    (F (0,1) (ContinuousLinearMap.snd ℝ ℂ ℂ))

theorem norm_hermitianObservationAssembly_le {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (F : (ℂ × ℂ) → ((ℂ × ℂ) →L[ℝ] ℂ) → Coeff q) (K : ℝ)
    (hF : ∀ v L, ‖L‖ ≤ 1 → ‖F v L‖ ≤ K*‖v‖) :
    ‖hermitianObservationAssembly F‖ ≤ 4*K := by
  have h00 := hF (1,0) (ContinuousLinearMap.fst ℝ ℂ ℂ) (ContinuousLinearMap.norm_fst_le ..)
  have h10 := hF (1,0) (ContinuousLinearMap.snd ℝ ℂ ℂ) (ContinuousLinearMap.norm_snd_le ..)
  have h01 := hF (0,1) (ContinuousLinearMap.fst ℝ ℂ ℂ) (ContinuousLinearMap.norm_fst_le ..)
  have h11 := hF (0,1) (ContinuousLinearMap.snd ℝ ℂ ℂ) (ContinuousLinearMap.norm_snd_le ..)
  simp only [Prod.norm_def,norm_one,norm_zero,max_eq_left zero_le_one,
    max_eq_right zero_le_one,mul_one] at h00 h10 h01 h11
  exact (norm_hermitianFourierAssembly_le _ _ _ _).trans (by linarith)

/-- Fourier coefficients of the actual full remainder M(z)-E_z. -/
def classicalHermitianRemainderFourierCoefficients {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) : HermitianCoeff q :=
  hermitianObservationAssembly (classicalSobolevRemainderFourierCoefficients hq a z)

/-- Every coefficient is the actual operator-valued Fourier integral. -/
theorem classicalHermitianRemainderFourierCoefficients_apply {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : 1 < q) (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) (k : ℤ) :
    classicalHermitianRemainderFourierCoefficients hq a z k =
      ∫ t in (0 : ℝ)..1, wave (-k) (2*t) •
        classicalHermitianRemainderOperator (classicalSobolevPotential a) z t := by
  simpa only [classicalHermitianRemainderFourierCoefficients,hermitianObservationAssembly,
    hermitianFourierAssembly_apply,classicalSobolevRemainderFourierCoefficients_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',classicalHermitianRemainderOperator]
    using hermitianColumns_intervalFourierCoefficient
      (classicalSolutionRemainder (classicalSobolevPotential a) z (1,0))
      (classicalSolutionRemainder (classicalSobolevPotential a) z (0,1))
      (continuous_classicalSolutionRemainder _ _ _) (continuous_classicalSolutionRemainder _ _ _) k

/-- The complete reference error M(z)-E_x, acting on Hermitian vectors. -/
def classicalHermitianShiftedFreeOperator (φ : Curve (ℂ × ℂ)) (z : ℂ) (x t : ℝ) :
    HermitianOperator :=
  hermitianColumns (classicalShiftedFreeRemainder φ z x (1,0) t)
    (classicalShiftedFreeRemainder φ z x (0,1) t)

theorem classicalHermitianShiftedFreeOperator_eq_matrix
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (x t : ℝ) :
    classicalHermitianShiftedFreeOperator φ z x t =
      classicalHermitianMatrixOperator (classicalFundamentalMatrix φ z t-classicalFreeMatrix x t) := by
  unfold classicalHermitianShiftedFreeOperator classicalHermitianMatrixOperator
  congr 1 <;> ext <;>
    simp [classicalShiftedFreeRemainder,classicalFreeVector,classicalFundamentalMatrix,classicalFreeMatrix]

/-- The full shifted-free Fourier sequence. -/
def classicalHermitianShiftedFreeFourierCoefficients {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) : HermitianCoeff q :=
  hermitianObservationAssembly (classicalShiftedFreeFourierCoefficients hq φ z x)

theorem classicalHermitianShiftedFreeFourierCoefficients_apply {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : 1 < q) (φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) (k : ℤ) :
    classicalHermitianShiftedFreeFourierCoefficients hq φ z x k =
      ∫ t in (0 : ℝ)..1, wave (-k) (2*t) • classicalHermitianShiftedFreeOperator φ z x t := by
  simpa only [classicalHermitianShiftedFreeFourierCoefficients,hermitianObservationAssembly,
    hermitianFourierAssembly_apply,classicalShiftedFreeFourierCoefficients_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',classicalHermitianShiftedFreeOperator,
    classicalShiftedFreeRemainder]
    using hermitianColumns_intervalFourierCoefficient
      (classicalShiftedFreeRemainder φ z x (1,0)) (classicalShiftedFreeRemainder φ z x (0,1))
      (contDiff_classicalShiftedFreeRemainder _ _ _ _).continuous
      (contDiff_classicalShiftedFreeRemainder _ _ _ _).continuous k

/-- Changing an equal exponent preserves the norm, including the literal q=2 API. -/
theorem norm_classicalHermitianRemainderFourierCoefficients_congr
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : 1 < p) (hq : 1 < q)
    (hpq : p = q) (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) :
    ‖classicalHermitianRemainderFourierCoefficients hp a z‖ =
      ‖classicalHermitianRemainderFourierCoefficients hq a z‖ := by
  subst q
  rfl

/-- Equal exponents also preserve the norm of the full shifted-free sequence. -/
theorem norm_classicalHermitianShiftedFreeFourierCoefficients_congr
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : 1 < p) (hq : 1 < q)
    (hpq : p = q) (φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) :
    ‖classicalHermitianShiftedFreeFourierCoefficients hp φ z x‖ =
      ‖classicalHermitianShiftedFreeFourierCoefficients hq φ z x‖ := by
  subst q
  rfl

/-- G.3 near-free Fourier decay for the full matrix, uniformly on H¹ balls. -/
theorem exists_classicalHermitianRemainder_sequence_fourier_decay
    (ε q : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 1+ε ≤ q) (hq2 : q ≤ 2)
    [Fact (1 ≤ ENNReal.ofReal q)] (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalHermitianRemainderFourierCoefficients (q := ENNReal.ofReal q)
        (ENNReal.one_lt_ofReal.mpr (by linarith)) a (ν n)‖ ≤
        4*classicalSobolevInterpolationConstant ε hε M B/
          (n.natAbs : ℝ)^(fundamentalFourierDecayExponent ε q) := by
  obtain ⟨N,hN,h⟩ := exists_classicalSobolevRemainder_sequence_fourier_decay
    ε q hε hε1 hq0 hq2 M B hB N₀
  refine ⟨N,hN,fun ν hν a ha n hn => ?_⟩
  apply (norm_hermitianObservationAssembly_le _
    (classicalSobolevInterpolationConstant ε hε M B/
      (n.natAbs : ℝ)^(fundamentalFourierDecayExponent ε q)) ?_).trans_eq (by ring)
  intro v L hL
  simpa only [div_mul_eq_mul_div] using h ν hν a ha v L hL n hn

/-- G.3 shifted-free decay, with the stronger inverse-index displacement hypothesis. -/
theorem exists_classicalHermitianShiftedFree_sequence_fourier_decay
    (ε q : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 1+ε ≤ q) (hq2 : q ≤ 2)
    [Fact (1 ≤ ENNReal.ofReal q)] (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ)) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalHermitianShiftedFreeFourierCoefficients (q := ENNReal.ofReal q)
        (ENNReal.one_lt_ofReal.mpr (by linarith)) (classicalSobolevPotential a) (ν n)
        (Real.pi*(n : ℝ))‖ ≤
        4*classicalShiftedFreeInterpolationConstant ε hε M B/
          (n.natAbs : ℝ)^(fundamentalFourierDecayExponent ε q) := by
  obtain ⟨N,hN,h⟩ := exists_classicalShiftedFree_sequence_fourier_decay
    ε q hε hε1 hq0 hq2 M B hB N₀
  refine ⟨N,hN,fun ν hν a ha n hn => ?_⟩
  apply (norm_hermitianObservationAssembly_le _
    (classicalShiftedFreeInterpolationConstant ε hε M B/
      (n.natAbs : ℝ)^(fundamentalFourierDecayExponent ε q)) ?_).trans_eq (by ring)
  intro v L hL
  simpa only [div_mul_eq_mul_div] using h ν hν a ha v L hL n hn

end NLS.ZakharovShabat
