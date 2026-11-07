import NLS.Articles.KdVPseudomeasures.SpectralInverseRestriction
import NLS.KdV.PseudomeasureRealGapComparison

/-! Actual canonical real gap comparison and the actual adapted Fourier tail
needed in source Section2.7. No open-gap or nonzero-coupling assumption is imposed. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The actual source alpha lies between the actual pair endpoints,and its
actual coupling is bounded below and above by the physical pair gap. -/
theorem SourceHillRealPair.adapted_gap_comparison (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (n : ℕ) (hn : 1 ≤ n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) (p : SourceHillRealPair r hr q n) :
    p.left ≤ (sourceDiagonalRoot r hr n hn q.val).re ∧
      (sourceDiagonalRoot r hr n hn q.val).re ≤ p.right ∧
      ‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1‖ ≤ p.right-p.left ∧
      p.right-p.left ≤ 3*‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1‖ := by
  have hC : sobolevConjugation (-r) ⊤ q.val = q.val := Subtype.ext q.property.1.symm
  have hqC : endpointConjugate SpectralWeight.one r (sourceEndpointCoefficients r q.val) = sourceEndpointCoefficients r q.val := by
    rw [← sourceEndpointCoefficients_conj, hC]
  have hh := EndpointHillRealPair.adapted_gap_comparison r hr.1 hr.2 n hn (sourceEndpointCoefficients r q.val)
    (by simpa only [norm_sourceEndpointCoefficients] using hs) hqC p
  simpa only [sourceAdaptedCouplings, sourceWeightedDiagonalRoot, sourceForgetUnitWeight_eq,
    LinearIsometryEquiv.symm_apply_apply, sourceEndpointEntries, sourceDiagonalRoot] using hh

/-- The coupling comparison is for the intrinsic actual canonical labels,
with their full physical multiplicities and exact usual high slots. -/
theorem source_canonical_adapted_gap_comparison (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (N : ℕ) (h : SourceHillRealLabeling r hr q N (sourceHillLabels r hr q))
    (n : ℕ) (hn : 1 ≤ n) (hN : N ≤ n) :
    sourceHillLabels r hr q (2*n-1) ≤ (sourceDiagonalRoot r hr n hn q.val).re ∧
      (sourceDiagonalRoot r hr n hn q.val).re ≤ sourceHillLabels r hr q (2*n) ∧
      ‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1‖ ≤
        ‖sourceCanonicalGapValues r hr q (n:ℤ)‖ ∧
      ‖sourceCanonicalGapValues r hr q (n:ℤ)‖ ≤
        3*‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1‖ := by
  obtain ⟨p, hl, hu⟩ := h.high_pair n hN
  have hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2 := by
    simpa only [norm_sourceEndpointCoefficients] using endpointHill_small_of_wide_small r hr.2 n
      (sourceEndpointCoefficients r q.val) (by simpa only [norm_sourceEndpointCoefficients] using h.cutoff_small n hN)
  have hh := SourceHillRealPair.adapted_gap_comparison r hr q n hn hs p
  have hn0 : (n:ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hg : ‖sourceCanonicalGapValues r hr q (n:ℤ)‖ = p.right-p.left := by
    simp only [sourceCanonicalGapValues, if_neg hn0, Int.natAbs_natCast, hl, hu,
      Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr p.ordered)]
  simpa only [hl, hu, hg] using hh

/-- Source Lemma2.20 for the REAL original potentials needed in Theorem2.2.
Both squared bounds include a collapsed gap;no ratio/nonzero assumption is needed. -/
theorem sourceLemma2_20_real (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (N : ℕ) (h : SourceHillRealLabeling r hr q N (sourceHillLabels r hr q))
    (n : ℕ) (hn : 1 ≤ n) (hN : N ≤ n) :
    ‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1*
      (sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).2‖ ≤
        ‖sourceCanonicalGapValues r hr q (n:ℤ)‖^2 ∧
      ‖sourceCanonicalGapValues r hr q (n:ℤ)‖^2 ≤
        9*‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1*
          (sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).2‖ := by
  have hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceUnitWeightEquiv r q.val‖ ≤ 1/2 := by
    rw [LinearIsometryEquiv.norm_map]
    simpa only [norm_sourceEndpointCoefficients] using endpointHill_small_of_wide_small r hr.2 n
      (sourceEndpointCoefficients r q.val) (by simpa only [norm_sourceEndpointCoefficients] using h.cutoff_small n hN)
  have hreal := sourceAdaptedCouplings_real SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val) hs
    (by simpa only [sourceUnitWeightEquiv_val] using q.property.1)
  have hp : ‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1*
      (sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).2‖ =
      ‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1‖^2 := by
    rw [hreal, norm_mul, Complex.norm_conj]
    ring
  obtain ⟨_, _, hl, hu⟩ := source_canonical_adapted_gap_comparison r hr q N h n hn hN
  rw [hp]
  constructor <;> nlinarith [norm_nonneg ((sourceAdaptedCouplings SpectralWeight.one r hr n hn
    (sourceUnitWeightEquiv r q.val)).1), norm_nonneg (sourceCanonicalGapValues r hr q (n:ℤ))]

/-- One cutoff BEFORE original potentials gives the actual canonical two-sided
coupling and squared-product gap estimates at every subsequent high mode. -/
theorem source_uniform_real_coupling_gap_comparison (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      ∀ (n : ℕ) (hn : 1 ≤ n), N ≤ n →
        (‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1‖ ≤
          ‖sourceCanonicalGapValues r hr q (n:ℤ)‖ ∧
          ‖sourceCanonicalGapValues r hr q (n:ℤ)‖ ≤
            3*‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1‖) ∧
        (‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1*
          (sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).2‖ ≤
            ‖sourceCanonicalGapValues r hr q (n:ℤ)‖^2 ∧
          ‖sourceCanonicalGapValues r hr q (n:ℤ)‖^2 ≤
            9*‖(sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).1*
              (sourceAdaptedCouplings SpectralWeight.one r hr n hn (sourceUnitWeightEquiv r q.val)).2‖) := by
  obtain ⟨N, hN, hc⟩ := source_uniform_canonical_labels r hr R
  refine ⟨N, hN, fun q hq n hn hnN => ?_⟩
  have hh := source_canonical_adapted_gap_comparison r hr q N (hc q hq) n hn hnN
  exact ⟨hh.2.2, sourceLemma2_20_real r hr q N (hc q hq) n hn hnN⟩

/-- The actual adapted Fourier map has each high real coefficient bounded by
the ACTUAL canonical gap. This is the inverse-spectral tail estimate for Omega. -/
theorem sourceAdaptedFourier_tail_le_canonical_gap (r : ℝ) (hr : AdmissiblePredualOrder r)
    (N : ℕ) (hN : 2 ≤ N) (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2)
    (q : Potential r) (hq : ‖q.val‖ ≤ R) (n : ℕ) (hn : N ≤ n) :
    ‖(sourceAdaptedFourier r hr N q.val).val (mode (-(2*(n:ℤ))))‖ ≤ ‖sourceCanonicalGapValues r hr q (n:ℤ)‖ ∧
      ‖(sourceAdaptedFourier r hr N q.val).val (mode (2*(n:ℤ)))‖ ≤ ‖sourceCanonicalGapValues r hr q (n:ℤ)‖ := by
  have hwide (k : ℕ) (hk : N ≤ k) : 13*endpointHillConstant r*(k:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2 := by
    have hc : 0 ≤ endpointHillConstant r*(k:ℝ)^(r-1/2) := by positivity [endpointHillConstant_pos r hr.2]
    have hh := hcut k (by omega) hk
    have hi := mul_le_mul_of_nonneg_left (show 13*‖q.val‖ ≤ 64*R by linarith [norm_nonneg q.val]) hc
    nlinarith
  have hlabel := sourceHillLabels_spec_at r hr q N hN hwide
  have hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceUnitWeightEquiv r q.val‖ ≤ 1/2 := by
    rw [LinearIsometryEquiv.norm_map]
    simpa only [norm_sourceEndpointCoefficients] using endpointHill_small_of_wide_small r hr.2 n
      (sourceEndpointCoefficients r q.val) (by simpa only [norm_sourceEndpointCoefficients] using hwide n hn)
  have hb := (source_canonical_adapted_gap_comparison r hr q N hlabel n (by omega) hn).2.2.1
  have hp := sourceWeightedAdaptedFourier_high_pair SpectralWeight.one r hr N R hR hcut
    (sourceUnitWeightEquiv r q.val) (((sourceUnitWeightEquiv r).norm_map _).trans_le hq) n (by omega) hn
  have hreal := sourceAdaptedCouplings_real SpectralWeight.one r hr n (by omega) (sourceUnitWeightEquiv r q.val)
    hsmall (by simpa only [sourceUnitWeightEquiv_val] using q.property.1)
  constructor
  · simpa only [sourceAdaptedFourier_val, hp.1] using hb
  · simpa only [sourceAdaptedFourier_val, hp.2, hreal, Complex.norm_conj] using hb

/-- A cutoff chosen BEFORE the original real potential gives the actual
adapted-map inverse tail bound in every later mode,with its quantitative
construction criterion retained for subsequent inverse regularity arguments. -/
theorem source_uniform_adapted_fourier_tail_gap_bound (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧
      (∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2) ∧
      ∀ q : Potential r, ‖q.val‖ ≤ R → ∀ n : ℕ, N ≤ n →
        ‖(sourceAdaptedFourier r hr N q.val).val (mode (-(2*(n:ℤ))))‖ ≤ ‖sourceCanonicalGapValues r hr q (n:ℤ)‖ ∧
        ‖(sourceAdaptedFourier r hr N q.val).val (mode (2*(n:ℤ)))‖ ≤ ‖sourceCanonicalGapValues r hr q (n:ℤ)‖ := by
  obtain ⟨N₀, _, hc⟩ := exists_endpointHill_cutoff r hr.2 (64*R)
  let N := max N₀ 2
  have hN : 2 ≤ N := le_max_right _ _
  have hcut (n : ℕ) (_ : 1 ≤ n) (hn : N ≤ n) := hc n ((le_max_left N₀ 2).trans hn)
  exact ⟨N, hN, hcut, fun q hq n hn => sourceAdaptedFourier_tail_le_canonical_gap r hr N hN R hR hcut q hq n hn⟩

end NLS.Articles.KdVPseudomeasures
