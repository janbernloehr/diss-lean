import NLS.ZakharovShabat.ClassicalHermitianTimeBounds
import NLS.ZakharovShabat.SourcePeriodicH1Norm

/-! # G.3 on the original complex period-one H¹ source

The full matrix estimates use actual operator-valued Fourier integrals and
the physical H¹ time norm. Bounds and cutoffs are uniform on balls in the
exact Chapter 5 source norm. The printed exponent is used for 0 < ε < 1;
the singular expression at ε = 1 is not assigned a source interpretation.
-/
noncomputable section
open Set NLS.Fourier NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The original period-one potential in the classical curve representation. -/
def sourceG3ClassicalCoefficients (a : ScalarDomain 2 × ScalarDomain 2) :
    ScalarDomain 2 × ScalarDomain 2 := (Coeff.periodDoubleSobolev a.1,Coeff.periodDoubleSobolev a.2)

/-- This is exactly the original source potential on the physical interval. -/
theorem sourceG3ClassicalCoefficients_potential (a : ScalarDomain 2 × ScalarDomain 2)
    (t : Icc (0 : ℝ) 1) :
    classicalSobolevPotential (sourceG3ClassicalCoefficients a) t = sourcePeriodicH1Potential a t := by
  simpa only [NLS.LinearVolterra.extend_coe,sourceG3ClassicalCoefficients] using (sourcePeriodicH1Potential_eq_classical a t).symm

/-- The existing coefficient norm is bounded by the exact source Fourier norm. -/
theorem norm_sourceG3ClassicalCoefficients_le (a : ScalarDomain 2 × ScalarDomain 2) :
    ‖sourceG3ClassicalCoefficients a‖ ≤
      2*‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ := by
  have hs (b : ScalarDomain 2) : ‖b‖ ≤
      ‖sourcePiSobolevScalar 1 1 le_rfl (higherSobolevSourceOneEquiv (b,0)).1‖ := by
    rw [WeightedCoeff.norm_eq]
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro n
    have hb : (higherSobolevSourceOneEquiv (b,0)).1.val n = b.val n := by
      change 1*b.val n = b.val n
      exact one_mul _
    simp only [WeightedCoeff.weightEquiv_apply,sourcePiSobolevScalar_apply,hb,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,Weight.sobolev_apply,Real.rpow_one]
    simp only [SpectralWeight.piSobolev_apply,Real.rpow_natCast,pow_one]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [abs_of_nonneg (by positivity : 0 ≤ 1+|(n : ℝ)|),
      abs_of_nonneg (by positivity : 0 ≤ 1+|((2*n : ℤ) : ℝ)*Real.pi|)]
    simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg (n : ℝ),Real.pi_gt_three]
  have h1 : ‖a.1‖ ≤ ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ :=
    (hs a.1).trans (WithLp.norm_fst_le _ (sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)))
  have h2 : ‖a.2‖ ≤ ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ :=
    (hs a.2).trans (WithLp.norm_snd_le _ (sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)))
  exact max_le
    ((Coeff.norm_periodDoubleSobolev_le a.1).trans (by linarith))
    ((Coeff.norm_periodDoubleSobolev_le a.2).trans (by linarith))

/-- G.3 H¹ time bound, uniform on exact source-norm balls and common displacement tails. -/
theorem sourceLemmaG3_H1 (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2),
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M →
      ∀ n : ℤ, N ≤ n.natAbs →
      hermitianIntervalH1Norm (classicalHermitianRemainderOperator
        (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n)) ≤
        4*(classicalSobolevErrorConstant (2*M) B+classicalSobolevDerivativeConstant (2*M) B) := by
  obtain ⟨N,hN,h⟩ := exists_classicalHermitianRemainder_sequence_H1_bound (2*M) B hB N₀
  refine ⟨N,hN,fun ν hν a ha n hn => h ν hν (sourceG3ClassicalCoefficients a) ?_ n hn⟩
  exact (norm_sourceG3ClassicalCoefficients_le a).trans (by linarith)

/-- G.3 Fourier–Lebesgue decay of the actual full remainder on all complex H¹ sources. -/
theorem sourceLemmaG3_fourier_decay
    (ε q : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 1+ε ≤ q) (hq2 : q ≤ 2)
    [Fact (1 ≤ ENNReal.ofReal q)] (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2),
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalHermitianRemainderFourierCoefficients (q := ENNReal.ofReal q)
        (ENNReal.one_lt_ofReal.mpr (by linarith)) (sourceG3ClassicalCoefficients a) (ν n)‖ ≤
        4*classicalSobolevInterpolationConstant ε hε (2*M) B/
          (n.natAbs : ℝ)^(fundamentalFourierDecayExponent ε q) := by
  obtain ⟨N,hN,h⟩ := exists_classicalHermitianRemainder_sequence_fourier_decay
    ε q hε hε1 hq0 hq2 (2*M) B hB N₀
  refine ⟨N,hN,fun ν hν a ha n hn => h ν hν (sourceG3ClassicalCoefficients a) ?_ n hn⟩
  exact (norm_sourceG3ClassicalCoefficients_le a).trans (by linarith)

/-- G.3 comparison with E_(nπ), under the stronger O(1/|n|) displacement hypothesis. -/
theorem sourceLemmaG3_shiftedFree_decay
    (ε q : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 1+ε ≤ q) (hq2 : q ≤ 2)
    [Fact (1 ≤ ENNReal.ofReal q)] (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ)) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2),
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalHermitianShiftedFreeFourierCoefficients (q := ENNReal.ofReal q)
        (ENNReal.one_lt_ofReal.mpr (by linarith))
        (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) (Real.pi*(n : ℝ))‖ ≤
        4*classicalShiftedFreeInterpolationConstant ε hε (2*M) B/
          (n.natAbs : ℝ)^(fundamentalFourierDecayExponent ε q) := by
  obtain ⟨N,hN,h⟩ := exists_classicalHermitianShiftedFree_sequence_fourier_decay
    ε q hε hε1 hq0 hq2 (2*M) B hB N₀
  refine ⟨N,hN,fun ν hν a ha n hn => h ν hν (sourceG3ClassicalCoefficients a) ?_ n hn⟩
  exact (norm_sourceG3ClassicalCoefficients_le a).trans (by linarith)

/-- The q=2 endpoint has inverse-index decay without any epsilon parameter. -/
theorem sourceLemmaG3_l2_decay (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2),
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalHermitianRemainderFourierCoefficients (q := 2) (by norm_num)
        (sourceG3ClassicalCoefficients a) (ν n)‖ ≤
        4*classicalSobolevInterpolationConstant (1/2) (by norm_num) (2*M) B/(n.natAbs : ℝ) := by
  have : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hα : fundamentalFourierDecayExponent (1/2) 2 = 1 := by
    norm_num [fundamentalFourierDecayExponent]
  have h := sourceLemmaG3_fourier_decay (1/2) 2 (by norm_num) (by norm_num) (by norm_num) le_rfl M B hB N₀
  simp_rw [norm_classicalHermitianRemainderFourierCoefficients_congr _ (by norm_num : (1 : ℝ≥0∞) < 2)
    (by norm_num : ENNReal.ofReal (2 : ℝ) = 2)] at h
  simpa only [hα,Real.rpow_one] using h

/-- The shifted-free q=2 endpoint also has inverse-index decay without epsilon. -/
theorem sourceLemmaG3_shiftedFree_l2_decay (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ)) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2),
        ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ ≤ M →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalHermitianShiftedFreeFourierCoefficients (q := 2) (by norm_num)
        (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) (ν n) (Real.pi*(n : ℝ))‖ ≤
        4*classicalShiftedFreeInterpolationConstant (1/2) (by norm_num) (2*M) B/(n.natAbs : ℝ) := by
  have : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hα : fundamentalFourierDecayExponent (1/2) 2 = 1 := by
    norm_num [fundamentalFourierDecayExponent]
  have h := sourceLemmaG3_shiftedFree_decay (1/2) 2 (by norm_num) (by norm_num) (by norm_num) le_rfl M B hB N₀
  simp_rw [norm_classicalHermitianShiftedFreeFourierCoefficients_congr _ (by norm_num : (1 : ℝ≥0∞) < 2)
    (by norm_num : ENNReal.ofReal (2 : ℝ) = 2)] at h
  simpa only [hα,Real.rpow_one] using h

end NLS.ZakharovShabat
