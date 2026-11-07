import NLS.Articles.KdVPseudomeasures.SpectralFreeCount
import NLS.KdV.PseudomeasureComplexCounting

/-!
# Uniform actual complex spectral counting on original endpoint norm balls

One zero-centered physical resolvent circle is constructed before the complex
potential is chosen. Its radius is the high free separator pi²N²-12N.
Homotopy of the actual original potential gives enclosed algebraic count2N-1.
The construction retains the full H1/H-minus-one operator and exact source norm.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The actual original complex high spectrum obeys the tight high-mode localization. -/
theorem sourceHillSpectrum_complex_high_cover (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (M : ℕ) (hM : 2 ≤ M)
    (hs : ∀ n : ℕ, M ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ sourceHillSpectrum r hr q)
    (hhigh : freeHillValue M-12*(M:ℝ) ≤ z.re) :
    ∃ n : ℕ, M ≤ n ∧ z ∈ reducedHillStrip n ∧ ‖z-(freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4 := by
  rw [sourceHillSpectrum_eq] at hz
  apply endpointHillSpectrum_complex_high_cover r hr.1 hr.2 (sourceEndpointCoefficients r q)
    M hM _ z hz hhigh
  intro n hn
  simpa only [norm_sourceEndpointCoefficients] using hs n hn

/-- A sufficiently large free separator circle excludes the full complex source spectrum. -/
theorem sourceComplexCircle_subset_resolvent (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hcut : ∀ n : ℕ, M ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*R ≤ 1/2)
    (hlarge : 2*(freeHillValue M-12*(M:ℝ))+4*sourceSpectralBound r hr R <
      freeHillValue N-12*(N:ℝ))
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) :
    sphere (0:ℂ) (freeHillValue N-12*(N:ℝ)) ⊆
      endpointHillResolventSet r hr.2 (sourceEndpointCoefficients r q) := by
  intro z hz
  by_contra hnot
  have hzsp : z ∈ sourceHillSpectrum r hr q := by
    rw [sourceHillSpectrum_eq]
    exact hnot
  have hnorm : ‖z‖ = freeHillValue N-12*(N:ℝ) := by
    simpa only [mem_sphere, dist_zero_right] using hz
  by_cases hhigh : freeHillValue M-12*(M:ℝ) ≤ z.re
  · have hs (n : ℕ) (hn : M ≤ n) :
        13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 := by
      apply le_trans _ (hcut n hn)
      exact mul_le_mul_of_nonneg_left hq (by positivity [endpointHillConstant_pos r hr.2])
    obtain ⟨n, hn, _, hloc⟩ := sourceHillSpectrum_complex_high_cover r hr q M hM hs z hzsp hhigh
    exact norm_ne_freeHillCentralEdge_of_localized N n hN (hM.trans hn) z hloc hnorm
  · have hbound := sourceHillSpectrum_norm_le_on_ball r hr R q hq z hzsp
    rw [hnorm] at hbound
    linarith

/-- One high circle works for every original complex potential in a specified norm ball. -/
theorem exists_sourceComplex_resolvent_circle (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      sphere (0:ℂ) (freeHillValue N-12*(N:ℝ)) ⊆
        endpointHillResolventSet r hr.2 (sourceEndpointCoefficients r q) := by
  obtain ⟨M, hM, hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (M:ℝ) (2*(freeHillValue M-12*(M:ℝ))+4*sourceSpectralBound r hr R))
  have hMN : M ≤ N := by
    have hm : (M:ℝ) < N := (le_max_left _ _).trans_lt hN
    exact_mod_cast hm.le
  have hN2 := hM.trans hMN
  refine ⟨N, hN2, fun q hq => sourceComplexCircle_subset_resolvent r hr R M N hM hN2 hcut ?_ q hq⟩
  exact ((le_max_right _ _).trans_lt hN).trans (natCast_lt_freeHillCentralEdge N hN2)

/-- The enclosed count is defined from the actual original complex algebraic root spaces. -/
def sourceComplexCircleAlgebraicCount (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) : ℕ :=
  endpointHillEnclosedAlgebraicCount r hr.1 hr.2 (sourceEndpointCoefficients r q)
    0 (freeHillValue N-12*(N:ℝ))

/-- The actual free enclosed count on the zero-centered circle is2N-1. -/
theorem sourceComplexCircleAlgebraicCount_zero (r : ℝ) (hr : AdmissiblePredualOrder r)
    (N : ℕ) (hN : 2 ≤ N) : sourceComplexCircleAlgebraicCount r hr 0 N = 2*N-1 := by
  have hs : endpointHillEnclosedSpectrum r hr.1 hr.2 (sourceEndpointCoefficients r 0)
      0 (freeHillValue N-12*(N:ℝ)) = sourceCentralSpectrum r hr 0 N := by
    ext z
    rw [mem_endpointHillEnclosedSpectrum, mem_sourceCentralSpectrum, ← sourceHillSpectrum_eq r hr 0]
    apply and_congr_right
    intro hz
    obtain ⟨n, rfl⟩ := (sourceHillSpectrum_zero_mem_iff r hr z).mp hz
    have hn : 0 ≤ freeHillValue n := by unfold freeHillValue; positivity
    simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hn, Complex.ofReal_re]
  unfold sourceComplexCircleAlgebraicCount endpointHillEnclosedAlgebraicCount
  rw [hs]
  have he := sourceCentralAlgebraicCount_zero r hr N hN
  simpa only [sourceCentralAlgebraicCount, sourceHillAlgebraicMultiplicity_eq r hr 0] using he

/-- Under a common complex norm-ball circle the actual count transports along
the original physical homotopy t*q, with no reality assumption. -/
theorem sourceComplexCircleAlgebraicCount_eq (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hc : ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      sphere (0:ℂ) (freeHillValue N-12*(N:ℝ)) ⊆
        endpointHillResolventSet r hr.2 (sourceEndpointCoefficients r q))
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) :
    sourceComplexCircleAlgebraicCount r hr q N = 2*N-1 := by
  let Q : ℝ → WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
    fun t => sourceEndpointCoefficients r ((t:ℂ) • q)
  have hQ : Continuous Q := (sourceEndpointCoefficientsCLM r).continuous.comp
    (Complex.continuous_ofReal.smul continuous_const)
  have hn (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖(t:ℂ) • q‖ ≤ R := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg q) ht.2).trans hq
  have he := endpointHillEnclosedAlgebraicCount_eq_on_preconnected r hr.1 hr.2 Q
    (Icc (0:ℝ) 1) isPreconnected_Icc hQ.continuousOn 0 (freeHillValue N-12*(N:ℝ))
    (freeHillCentralEdge_pos N hN) (fun t ht => hc _ (hn t ht))
    (a := 1) (b := 0) (by norm_num) (by norm_num)
  have h1 : Q 1 = sourceEndpointCoefficients r q := by simp only [Q, Complex.ofReal_one, one_smul]
  have h0 : Q 0 = sourceEndpointCoefficients r 0 := by simp only [Q, Complex.ofReal_zero, zero_smul]
  rw [h1, h0] at he
  exact he.trans (sourceComplexCircleAlgebraicCount_zero r hr N hN)

/-- One cutoff chosen BEFORE every complex original potential gives the ACTUAL
enclosed algebraic count2N-1 and a full physical resolvent circle on the norm ball. -/
theorem source_uniform_complex_algebraic_count (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      sphere (0:ℂ) (freeHillValue N-12*(N:ℝ)) ⊆
        endpointHillResolventSet r hr.2 (sourceEndpointCoefficients r q) ∧
      sourceComplexCircleAlgebraicCount r hr q N = 2*N-1 := by
  obtain ⟨N, hN, hc⟩ := exists_sourceComplex_resolvent_circle r hr R
  exact ⟨N, hN, fun q hq => ⟨hc q hq, sourceComplexCircleAlgebraicCount_eq r hr R N hN hc q hq⟩⟩

end NLS.Articles.KdVPseudomeasures
