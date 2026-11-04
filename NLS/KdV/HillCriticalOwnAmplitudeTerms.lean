import NLS.KdV.HillCriticalComplexOwnAmplitudeTails

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The critical source normalization agrees with the existing weighted
spectral coordinates: weight times sqrt(2*pi*n) times the original amplitude. -/
def hillNativeCriticalOwnAmplitudeTerm (w : SpectralWeight) (n : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : ℂ :=
  (w (2*(n : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*(n : ℝ)) : ℂ)*
    hillComplexOwnCartesianAmplitude h0q h0r n (hillPeriodOneCoefficientMap w q)

def hillNativeCriticalOwnDualAmplitudeTerm (w : SpectralWeight) (n : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : ℂ :=
  (w (2*(n : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*(n : ℝ)) : ℂ)*
    hillComplexOwnCartesianDualAmplitude h0q h0r n (hillPeriodOneCoefficientMap w q)

theorem norm_hillNativeCriticalOwnAmplitudeTerm_sq (w : SpectralWeight) (n : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) :
    ‖hillNativeCriticalOwnAmplitudeTerm h0q h0r w n q‖^2 =
      (2*Real.pi)*((n : ℝ)*(w (2*(n : ℤ)))^2*
        ‖hillComplexOwnCartesianAmplitude h0q h0r n (hillPeriodOneCoefficientMap w q)‖^2) := by
  rw [hillNativeCriticalOwnAmplitudeTerm,norm_mul,norm_mul,mul_pow,mul_pow,
    norm_real,Real.norm_eq_abs,sq_abs,norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by positivity)]
  ring

theorem norm_hillNativeCriticalOwnDualAmplitudeTerm_sq (w : SpectralWeight) (n : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) :
    ‖hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w n q‖^2 =
      (2*Real.pi)*((n : ℝ)*(w (2*(n : ℤ)))^2*
        ‖hillComplexOwnCartesianDualAmplitude h0q h0r n (hillPeriodOneCoefficientMap w q)‖^2) := by
  rw [hillNativeCriticalOwnDualAmplitudeTerm,norm_mul,norm_mul,mul_pow,mul_pow,
    norm_real,Real.norm_eq_abs,sq_abs,norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by positivity)]
  ring

/-- Scalar analyticity uses the original common complex own-amplitude
charts, with a common cutoff preceding the weight quantifier. -/
theorem exists_hillNativeCriticalOwnAmplitudeTerms_common_analytic (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ w : SpectralWeight, ∀ n : ℕ, N≤n →
      AnalyticOnNhd ℂ (hillNativeCriticalOwnAmplitudeTerm h0q h0r w n)
        (ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) ∧
      AnalyticOnNhd ℂ (hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w n)
        (ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) := by
  obtain ⟨C,hC,hcharts⟩ := exists_hillComplexOwnCartesianAmplitudes_common_analytic_bound h0q h0r
  obtain ⟨N,hN,hchart⟩ := hcharts B
  refine ⟨N,hN,?_⟩
  intro w n hn
  have hparam (q : WeightedCoeff w.doubleIndex.toWeight 2)
      (hq : q∈ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) :
      hillPeriodOneCoefficientMap w q∈ball (0 : Coeff 2) B := by
    rw [mem_ball,dist_zero_right]
    exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt
      (show ‖q‖<B by simpa only [mem_ball,dist_zero_right] using hq)
  constructor
  · intro q hq
    exact analyticAt_const.mul (((hchart n hn).1 _ (hparam q hq)).comp
      (f := hillPeriodOneCoefficientMap w) ((hillPeriodOneCoefficientMap w).analyticAt q))
  · intro q hq
    exact analyticAt_const.mul (((hchart n hn).2.1 _ (hparam q hq)).comp
      (f := hillPeriodOneCoefficientMap w) ((hillPeriodOneCoefficientMap w).analyticAt q))

/-- The genuine critical normalized square sums are uniformly bounded on
complex source balls for both original own amplitudes. -/
theorem exists_hillNativeCriticalOwnAmplitudeTerms_uniform_square_bound
    (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0<C ∧ ∃ N0 : ℕ, 1≤N0 ∧ ∀ w : SpectralWeight, ∀ N : ℕ, N0≤N →
      ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖≤B →
      (Summable (fun k : ℕ => ‖hillNativeCriticalOwnAmplitudeTerm h0q h0r w (k+N) q‖^2) ∧
        (∑' k : ℕ, ‖hillNativeCriticalOwnAmplitudeTerm h0q h0r w (k+N) q‖^2)≤C*(B^2+512*B^4)) ∧
      (Summable (fun k : ℕ => ‖hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w (k+N) q‖^2) ∧
        (∑' k : ℕ, ‖hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w (k+N) q‖^2)≤C*(B^2+512*B^4)) := by
  obtain ⟨C,hC,N0,hN0,htail⟩ :=
    exists_hillComplexOwnCartesianAmplitudes_native_critical_tail_bound h0q h0r B hB
  refine ⟨2*Real.pi*C,by positivity,N0,hN0,?_⟩
  intro w N hN q hq
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN0.trans hN
  have hq2 : ‖q‖^2≤B^2 := pow_le_pow_left₀ (norm_nonneg q) hq 2
  have hq4 : ‖q‖^4≤B^4 := pow_le_pow_left₀ (norm_nonneg q) hq 4
  have hft := Coeff.norm_fourierTail_le (by norm_num : (2 : ℝ≥0∞)≠0) N
    (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)
  rw [← WeightedCoeff.norm_eq] at hft
  have hft2 := pow_le_pow_left₀ (norm_nonneg _) hft 2
  have hrem : 512*C*‖q‖^4/(N : ℝ)≤512*C*‖q‖^4 := div_le_self (by positivity) hNR
  have hmajor : C*‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2+
      512*C*‖q‖^4/(N : ℝ)≤C*(B^2+512*B^4) := by
    nlinarith [mul_le_mul_of_nonneg_left hq2 hC.le,mul_le_mul_of_nonneg_left hq4 hC.le,
      mul_le_mul_of_nonneg_left hft2 hC.le]
  obtain ⟨⟨hsp,hbp⟩,⟨hsm,hbm⟩⟩ := htail w q hq N hN
  constructor
  · simp_rw [norm_hillNativeCriticalOwnAmplitudeTerm_sq]
    refine ⟨hsp.mul_left (2*Real.pi),?_⟩
    rw [tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left (hbp.trans hmajor) (by positivity)).trans_eq (by ring)
  · simp_rw [norm_hillNativeCriticalOwnDualAmplitudeTerm_sq]
    refine ⟨hsm.mul_left (2*Real.pi),?_⟩
    rw [tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left (hbm.trans hmajor) (by positivity)).trans_eq (by ring)

/-- On real source potentials the same terms are exactly the original
normalized physical own amplitudes and their conjugates. -/
theorem exists_hillNativeCriticalOwnAmplitudeTerms_real_physical_matching (B : ℝ) :
    ∃ N : ℕ, ∃ hN : 1≤N, ∀ w : SpectralWeight,
      ∀ q : RealHillWeightedPotential w, ‖q.val‖≤B → ∀ n : ℕ, ∀ hn : N≤n,
      hillNativeCriticalOwnAmplitudeTerm h0q h0r w n q.val =
        (w (2*(n : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*(n : ℝ)) : ℂ)*
          hillOwnCartesianAmplitude (hillPeriodOneUnitPotential w q.val)
            (hillPeriodOneUnitPotential_even w q.val) (hillPeriodOneUnitPotential_real w q.val q.property)
            n (hN.trans hn) ∧
      hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w n q.val =
        (w (2*(n : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*(n : ℝ)) : ℂ)*
          (starRingEnd ℂ) (hillOwnCartesianAmplitude (hillPeriodOneUnitPotential w q.val)
            (hillPeriodOneUnitPotential_even w q.val) (hillPeriodOneUnitPotential_real w q.val q.property)
            n (hN.trans hn)) := by
  obtain ⟨N,hN,hmatch⟩ := exists_hillComplexOwnCartesianAmplitudes_bounded_real_physical_matching h0q h0r B
  refine ⟨N,hN,?_⟩
  intro w q hq n hn
  have hp : ‖SpectralWeight.one.toCoeff (hillPeriodOneUnitPotential w q.val)‖≤B := by
    rw [← hillPeriodOneCoefficientMap_eq_unit]
    exact (norm_hillPeriodOneCoefficientMap_le w q.val).trans hq
  have hm := hmatch _ (hillPeriodOneUnitPotential_even w q.val)
    (hillPeriodOneUnitPotential_real w q.val q.property) hp n hn
  constructor
  · rw [hillNativeCriticalOwnAmplitudeTerm,hillPeriodOneCoefficientMap_eq_unit,hm.1]
  · rw [hillNativeCriticalOwnDualAmplitudeTerm,hillPeriodOneCoefficientMap_eq_unit,hm.2]

end NLS.KdV
