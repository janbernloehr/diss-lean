import NLS.Articles.KdVPseudomeasures.SourceWideStripReduction
import NLS.Articles.KdVPseudomeasures.SpectralComplexPairs
import NLS.KdV.PseudomeasureWideComplexPairs

/-! Full printed-strip source Lemmas 2.7 and 2.11. The determinant is the
original proof-independent analytic source family, and the repetitions
are the full original physical algebraic multiplicities. -/
noncomputable section
open Set NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem source_rootDisc_subset_printedStrip (n : ℕ) (hn : 1≤n) :
    Metric.closedBall (freeHillValue n:ℂ) (4*Real.sqrt (n:ℝ)) ⊆ printedHillStrip n := by
  intro z hz
  have hnorm : ‖z-(freeHillValue n:ℂ)‖ ≤ 4*Real.sqrt (n:ℝ) := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hRe := Complex.abs_re_le_norm (z-(freeHillValue n:ℂ))
  simp only [Complex.sub_re,Complex.ofReal_re] at hRe
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hsq : Real.sqrt (n:ℝ)≤n := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  change |z.re-freeHillValue n| ≤ 12*(n:ℝ)
  nlinarith

theorem sourceLemma2_7_fullPrintedStrip (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2≤N ∧
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖≤R →
      ∀ (n : ℕ) (_hn : 2≤n), N≤n → ∀ (z : ℂ) (_hz : z ∈ printedHillStrip n),
        sourceEndpointDeterminant r hr n (q,z)=0 ↔
          ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f≠0 ∧
            singularHillOperator (sourceComplexHminusOne r hr q) f=z • singularHillDomainInclusion f := by
  obtain ⟨N,hN,h⟩ := sourceLemma2_7_wide r hr R
  refine ⟨N,hN,?_⟩
  intro q hq n hn hNn z hz
  obtain ⟨hs,hiff⟩ := h q hq n hn hNn z hz
  have he := endpointReducedFamily_eq_wide r hr.1 hr.2 n hn (sourceEndpointCoefficients r q,z) hz hs
  change (endpointReducedFamily r hr.1 hr.2 n (sourceEndpointCoefficients r q,z)).toLinearMap.det=0 ↔ _
  rw [he]
  exact hiff

theorem sourceLemma2_11_wide (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2≤N ∧
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖≤R →
      ∀ (n : ℕ) (_hn : 2≤n), N≤n →
      WideEndpointSpectralResult r hr.1 hr.2 n (sourceEndpointCoefficients r q) := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn hNn
  have hC : 0 ≤ 13*endpointHillConstant r*(n:ℝ)^(r-1/2) :=
    mul_nonneg (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr.2).le)
      (Real.rpow_nonneg (by positivity) _)
  have hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    rw [norm_sourceEndpointCoefficients]
    exact (mul_le_mul_of_nonneg_left hq hC).trans (hcut n hNn)
  exact wideEndpointSpectralResult r hr.1 hr.2 n hn (sourceEndpointCoefficients r q) hs

end NLS.Articles.KdVPseudomeasures
