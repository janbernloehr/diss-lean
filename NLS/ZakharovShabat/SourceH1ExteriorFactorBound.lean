import NLS.ZakharovShabat.SourceExteriorCriticalFactorBound
import NLS.ZakharovShabat.QuadraticSpectralBox
import NLS.ZakharovShabat.SourceRealTypeBanachSpace

/-! # H¹ localization applied to the actual exterior critical-root factors

Both indices satisfy the original quadratic localization threshold. The
spectral parameter ranges over the entire target gap. Complex sources
retain an explicit critical-offset hypothesis; real sources discharge it
using critical-point membership in the canonical gap, even at closed gaps.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace NLS.ZakharovShabat

/-- The entire complex H¹ gap is contained in its localization disc. -/
theorem sourceH1_gap_point_norm_localization (ψ : CoeffPair 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ n) :
    ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/5 := by
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0 :=
    hφ ▸ periodOnePotential_mem ψ
  have h := (H1_periodicSpectrum_uniform_localization φ heven).1 n hn
  simp only [hφ] at h
  exact gap_segment_norm_sub_le _ _ z _ _ (h.1.trans h.2.2.le) (h.2.1.trans h.2.2.le) hz

/-- The high-index factor bound for a complex H¹ source with controlled critical offset. -/
theorem sourceH1_exterior_critical_factor_le (ψ : CoeffPair 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ)
    (m n : ℤ) (hmn : m ≠ n)
    (hm : 8*‖φ‖^2 ≤ 1+|(m:ℝ)|) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ n)
    (hc : ‖canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) m-
      canonicalPeriodicMidpoint (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖ ≤
      ‖canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖) :
    ‖(canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
      sourceStandardRoot (by simp) (by norm_num) ψ m z‖ ≤
      1+‖canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖/
        |((m-n:ℤ):ℝ)| := by
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0 :=
    hφ ▸ periodOnePotential_mem ψ
  have h := (H1_periodicSpectrum_uniform_localization φ heven).1 m hm
  simp only [hφ] at h
  exact source_exterior_critical_factor_le (by simp) (by norm_num) ψ m n z hmn
    (h.1.trans h.2.2.le) (h.2.1.trans h.2.2.le)
    (sourceH1_gap_point_norm_localization ψ φ hφ n hn z hz) hc

/-- On real sources the critical-offset hypothesis is automatic, including closed gaps. -/
theorem sourceH1_real_exterior_critical_factor_le (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (m n : ℤ) (hmn : m ≠ n)
    (hm : 8*‖φ‖^2 ≤ 1+|(m:ℝ)|) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ.val n) :
    ‖(canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m-z)/
      sourceStandardRoot (by simp) (by norm_num) ψ.val m z‖ ≤
      1+‖canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m‖/
        |((m-n:ℤ):ℝ)| := by
  apply sourceH1_exterior_critical_factor_le ψ.val φ hφ m n hmn hm hn z hz
  have hc := sourceCanonicalCriticalPoint_mem_periodicSegment_of_realType
    (by simp) (by norm_num) m ψ.val ψ.property
  exact (gap_segment_midpoint_dist_le _ _ _ hc).trans (by
    change ‖canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m‖/2 ≤ _
    linarith [norm_nonneg (canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m)])

/-- Every finite exterior product obeys the square-budget bound on the entire target gap. -/
theorem sourceH1_real_exterior_product_le_exp_sqrt_budgets (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (s : Finset ℤ) (n : ℤ) (hs : n ∉ s)
    (hm : ∀ m ∈ s, 8*‖φ‖^2 ≤ 1+|(m:ℝ)|) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ.val n)
    (G R : ℝ)
    (hG : ∑ m ∈ s, ‖canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m‖^2 ≤ G)
    (hR : ∑ m ∈ s, (1/|((m-n:ℤ):ℝ)|)^2 ≤ R) :
    ‖∏ m ∈ s, (canonicalCriticalPoints (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m-z)/
      sourceStandardRoot (by simp) (by norm_num) ψ.val m z‖ ≤
      Real.exp (Real.sqrt G*Real.sqrt R) := by
  apply norm_finite_product_le_exp_sqrt_budgets s _
    (fun m => ‖canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m‖)
    (fun m => 1/|((m-n:ℤ):ℝ)|) G R _ hG hR
  intro m hms
  have hmn : m ≠ n := fun he => hs (he ▸ hms)
  simpa only [one_div,div_eq_mul_inv,one_mul] using
    sourceH1_real_exterior_critical_factor_le ψ φ hφ m n hmn (hm m hms) hn z hz

end NLS.ZakharovShabat
