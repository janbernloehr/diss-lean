import NLS.Articles.KdVPseudomeasures.SpectralCentralProjection
import NLS.KdV.PseudomeasureRieszRange

/-!
# The actual central algebraic count on the original singular source

The actual Riesz range is the sum of the original enclosed physical root
spaces. Their independence identifies its rank with the actual algebraic
count. Rank transport and the proved free baseline then give 2N-1.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- An original physical resolvent point has no actual full root vectors. -/
theorem sourceHillRootSpaceTop_eq_bot_of_not_mem_spectrum (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) (hz : z ∉ sourceHillSpectrum r hr q) :
    singularHillRootSpaceTop (sourceComplexHminusOne r hr q) z = ⊥ := by
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
  apply endpointHillRootSpaceTop_eq_bot_of_mem_resolvent r hr.2 (sourceEndpointCoefficients r q) z
  rw [sourceHillSpectrum_eq] at hz
  exact not_not.mp hz

/-- Independence is for the actual original root spaces, without a reality restriction. -/
theorem independent_sourceHillRootSpaceTop (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    iSupIndep (fun z : ℂ => singularHillRootSpaceTop (sourceComplexHminusOne r hr q) z) := by
  obtain ⟨a,ha⟩ := endpointHillResolventSet_nonempty r hr.1 hr.2 (sourceEndpointCoefficients r q)
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
  exact independent_endpointHillRootSpaceTop r hr.2 (sourceEndpointCoefficients r q) a ha

/-- The central projection range is exactly the sum over the existing actual finite central spectrum. -/
theorem sourceCentralProjection_range_eq_roots (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hcut : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*R ≤ 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) (hreal : q.val = q.val.conjugate) :
    (sourceCentralProjection r hr R N q).range =
      ⨆ z : sourceCentralSpectrum r hr q N, singularHillRootSpaceTop (sourceComplexHminusOne r hr q) z.val := by
  obtain ⟨a,ha⟩ := endpointHillResolventSet_nonempty r hr.1 hr.2 (sourceEndpointCoefficients r q)
  have hnative : (endpointHillHminusOne SpectralWeight.one r hr.2 (sourceEndpointCoefficients r q)).val =
      (endpointHillHminusOne SpectralWeight.one r hr.2 (sourceEndpointCoefficients r q)).val.conjugate := by
    rw [sourceEndpointCoefficients_HminusOne_complex r hr q,sourceComplexHminusOne_val r hr q]
    exact hreal
  have he := endpointHillRieszProjection_range_eq_roots r hr.2 (sourceEndpointCoefficients r q)
    hnative (sourceCentralCircleCenter r hr R N) (sourceCentralCircleRadius r hr R N)
    (sourceCentralCircleRadius_pos r hr R N hN)
    (sourceCentralCircle_subset_resolvent r hr R N hN hcut q hq hreal) a ha
  rw [sourceEndpointCoefficients_HminusOne_complex r hr q] at he
  change (endpointHillRieszProjection r hr.2 (sourceEndpointCoefficients r q)
    (sourceCentralCircleCenter r hr R N) (sourceCentralCircleRadius r hr R N)).range = _
  rw [he]
  apply le_antisymm
  · apply iSup_le
    intro z
    by_cases hz : z.val ∈ sourceHillSpectrum r hr q
    · have hm := (sourceHillSpectrum_mem_centralCircle_iff r hr R N q hq hreal z.val hz).mp z.property
      exact le_iSup_of_le ⟨z.val,hm⟩ le_rfl
    · rw [sourceHillRootSpaceTop_eq_bot_of_not_mem_spectrum r hr q z.val hz]
      exact bot_le
  · apply iSup_le
    intro z
    have hs := ((mem_sourceCentralSpectrum r hr q N z.val).mp z.property).1
    have hm := (sourceHillSpectrum_mem_centralCircle_iff r hr R N q hq hreal z.val hs).mpr z.property
    exact le_iSup_of_le ⟨z.val,hm⟩ le_rfl

/-- Actual projection rank equals the sum of ACTUAL physical algebraic multiplicities. -/
theorem sourceCentralProjection_rank_eq_count (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hcut : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*R ≤ 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) (hreal : q.val = q.val.conjugate) :
    Module.finrank ℂ (sourceCentralProjection r hr R N q).range = sourceCentralAlgebraicCount r hr q N := by
  let V := fun z : sourceCentralSpectrum r hr q N =>
    singularHillRootSpaceTop (sourceComplexHminusOne r hr q) z.val
  let (z : sourceCentralSpectrum r hr q N) : FiniteDimensional ℂ (V z) :=
    finiteDimensional_sourceHillRootSpaceTop r hr q z.val
  have hind : iSupIndep V := (independent_sourceHillRootSpaceTop r hr q).comp Subtype.val_injective
  have he := NLS.FunctionalAnalysis.finrank_iSup_of_iSupIndep V hind
  rw [← sourceCentralProjection_range_eq_roots r hr R N hN hcut q hq hreal] at he
  change Module.finrank ℂ (sourceCentralProjection r hr R N q).range =
    ∑ z : sourceCentralSpectrum r hr q N, sourceHillAlgebraicMultiplicity r hr q z.val at he
  simpa only [sourceCentralAlgebraicCount,Finset.sum_coe_sort] using he

/-- Exact central counting for every original native real potential on the norm ball. -/
theorem sourceCentralAlgebraicCount_eq (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hcut : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*R ≤ 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) (hreal : q.val = q.val.conjugate) :
    sourceCentralAlgebraicCount r hr q N = 2*N-1 := by
  have hzero : ‖(0 : FourierLebesgueSpace (2:ℝ) (-r) ⊤)‖ ≤ R := by
    simpa only [norm_zero] using (norm_nonneg q).trans hq
  have hrealzero : (0 : FourierLebesgueSpace (2:ℝ) (-r) ⊤).val =
      (0 : FourierLebesgueSpace (2:ℝ) (-r) ⊤).val.conjugate := by
    ext f
    change (0:ℂ) = star (0:ℂ)
    simp
  calc
    _ = Module.finrank ℂ (sourceCentralProjection r hr R N q).range :=
      (sourceCentralProjection_rank_eq_count r hr R N hN hcut q hq hreal).symm
    _ = Module.finrank ℂ (sourceCentralProjection r hr R N 0).range :=
      sourceCentralProjection_rank_eq_zero r hr R N hN hcut q hq hreal
    _ = sourceCentralAlgebraicCount r hr 0 N :=
      sourceCentralProjection_rank_eq_count r hr R N hN hcut 0 hzero hrealzero
    _ = 2*N-1 := sourceCentralAlgebraicCount_zero r hr N hN

/-- One original norm-ball cutoff gives the exact physical central count before q is chosen. -/
theorem source_uniform_central_algebraic_count (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      q.val = q.val.conjugate → sourceCentralAlgebraicCount r hr q N = 2*N-1 := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  exact ⟨N,hN,fun q hq hreal => sourceCentralAlgebraicCount_eq r hr R N hN (hcut N le_rfl) q hq hreal⟩

/-- The same cutoff gives the exact algebraic count below EVERY subsequent high separator.
This fixes the low-mode offset for the entire tail, with q chosen only after the cutoff. -/
theorem source_uniform_all_central_algebraic_counts (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      q.val = q.val.conjugate → ∀ n : ℕ, N ≤ n →
        sourceCentralAlgebraicCount r hr q n = 2*n-1 := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  exact ⟨N,hN,fun q hq hreal n hn => sourceCentralAlgebraicCount_eq r hr R n
    (hN.trans hn) (hcut n hn) q hq hreal⟩

end NLS.Articles.KdVPseudomeasures
