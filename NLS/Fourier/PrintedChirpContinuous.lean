import NLS.Fourier.PrintedChirpPolynomials
import NLS.Fourier.DyadicPrefixConvergence

/-! # The literal A.5 series has a continuous physical realization -/
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped ENNReal
namespace NLS.Fourier

/-- Ordinary cutoffs of the printed series converge in the continuous-function norm. -/
theorem exists_printedChirpContinuous :
    ∃ F : C(AddCircle (2 : ℝ),ℂ), Tendsto printedChirpPartialSum atTop (𝓝 F) :=
  exists_tendsto_of_dyadic_prefix_bounds printedChirpPartialSum
    (fun k => chirpDyadicBoundConstant/(k : ℝ)^(3/2 : ℝ)) summable_chirp_dyadic_majorant
    (fun k hk M hM => norm_printedChirpPartialSum_dyadic_prefix k M hk hM)

/-- The continuous limit of the particular series printed in the proof of A.5. -/
def printedChirpContinuous : C(AddCircle (2 : ℝ),ℂ) :=
  Classical.choose exists_printedChirpContinuous

theorem tendsto_printedChirpPartialSum :
    Tendsto printedChirpPartialSum atTop (𝓝 printedChirpContinuous) :=
  Classical.choose_spec exists_printedChirpContinuous

/-- The same convergence is uniform in the physical circle coordinate. -/
theorem tendstoUniformly_printedChirpPartialSum :
    TendstoUniformly (fun M y => printedChirpPartialSum M y) printedChirpContinuous atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have ht := (Metric.tendsto_nhds.mp tendsto_printedChirpPartialSum) ε hε
  filter_upwards [ht] with M hM
  intro y
  exact (ContinuousMap.dist_apply_le_dist y).trans_lt (by simpa only [dist_comm] using hM)

/-- Real physical coordinates inherit uniform convergence on the whole real line. -/
theorem tendstoUniformly_printedChirpPartialSum_real :
    TendstoUniformly (fun M (x : ℝ) => printedChirpPartialSum M (x : AddCircle (2 : ℝ)))
      (fun x : ℝ => printedChirpContinuous (x : AddCircle (2 : ℝ))) atTop :=
  tendstoUniformly_printedChirpPartialSum.comp (fun x : ℝ => (x : AddCircle (2 : ℝ)))

private def chirpCoefficientCLM (m : ℤ) : C(AddCircle (2 : ℝ),ℂ) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).comp continuousFourierCLM

private theorem chirpCoefficientCLM_apply (m : ℤ) (f : C(AddCircle (2 : ℝ),ℂ)) :
    chirpCoefficientCLM m f = fourierCoeff f m := continuousFourierCLM_apply f m

private theorem chirpCoefficientCLM_term (m : ℤ) (n : ℕ) :
    chirpCoefficientCLM m (printedChirpTerm n) =
      if (n : ℤ) = m then printedChirpCoefficient n else 0 := by
  rw [chirpCoefficientCLM_apply]
  simp only [printedChirpTerm,ContinuousMap.coe_smul,fourierCoeff.const_smul,
    fourierCoeff_fourier,Pi.single_apply,smul_eq_mul]
  split_ifs <;> simp_all

/-- Every physical Fourier coefficient of the continuous limit is the literal printed one. -/
theorem fourierCoeff_printedChirpContinuous (m : ℤ) :
    fourierCoeff printedChirpContinuous m = printedChirpCoefficient m := by
  have ht := (chirpCoefficientCLM m).continuous.tendsto printedChirpContinuous |>.comp
    tendsto_printedChirpPartialSum
  have he : ∀ᶠ M : ℕ in atTop,
      chirpCoefficientCLM m (printedChirpPartialSum M) = printedChirpCoefficient m := by
    by_cases hm : 0 ≤ m
    · let j := m.toNat
      have hj : (j : ℤ) = m := Int.toNat_of_nonneg hm
      filter_upwards [eventually_gt_atTop j] with M hM
      rw [printedChirpPartialSum,map_sum]
      simp only [chirpCoefficientCLM_term]
      rw [Finset.sum_eq_single j]
      · simp only [hj,ite_true]
      · intro b _ hbj
        have hbm : (b : ℤ) ≠ m := by
          intro h
          apply hbj
          exact_mod_cast h.trans hj.symm
        simp only [if_neg hbm]
      · intro hjM
        exact (hjM (Finset.mem_range.mpr hM)).elim
    · apply Eventually.of_forall
      intro M
      rw [printedChirpPartialSum,map_sum]
      have hnm (n : ℕ) : (n : ℤ) ≠ m := by omega
      simp only [chirpCoefficientCLM_term,if_neg (hnm _),Finset.sum_const_zero]
      simp [printedChirpCoefficient,show ¬2 ≤ m by omega]
  have hconst : Tendsto (fun M => chirpCoefficientCLM m (printedChirpPartialSum M))
      atTop (𝓝 (printedChirpCoefficient m)) := tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
  simpa only [chirpCoefficientCLM_apply] using tendsto_nhds_unique ht hconst

/-- The continuous sum represents exactly the previously constructed physical L2 function. -/
theorem toLp_printedChirpContinuous :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ printedChirpContinuous = printedChirpL2 := by
  apply fourierBasis.repr.injective
  ext n
  rw [fourierBasis_repr,fourierCoeff_toLp,fourierCoeff_printedChirpContinuous,
    fourierBasis_repr,fourierCoeff_printedChirpL2]

/-- The continuous printed witness has the sharp Fourier-Lebesgue threshold. -/
theorem memlp_fourierCoeff_printedChirpContinuous_iff {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Memℓp (fourierCoeff printedChirpContinuous) p ↔ 2 ≤ p := by
  simp only [show fourierCoeff printedChirpContinuous = printedChirpCoefficient from
    funext fourierCoeff_printedChirpContinuous,memlp_printedChirpCoefficient_iff]

end NLS.Fourier
