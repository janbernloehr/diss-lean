import NLS.SequenceSpaces.PeriodOneMiuraQuadratic
import NLS.ComplexAnalysis.SmallQuadraticInverse

/-! # Analytic shifted Miura charts near every complex H^-1 potential

For any bounded H^-1 ball, all sufficiently large masses give a local
analytic right inverse at every point of that ball. The mass is selected
before the potential. The target is the actual weighted Fourier space;
the chart solves the coefficient identity v' + (m+1)v + v² = q.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS

/-- Uniformly large masses admit analytic right inverses throughout any bounded ball. -/
theorem exists_periodOneMiuraCharts_on_bounded_ball {B : ℝ} (hB : 0 ≤ B) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ q : PeriodOneHminusOne, ‖q‖ ≤ B →
      ∃ v : Coeff 2, ‖v‖ ≤ 4*B+1 ∧ periodOneShiftedMiura m v = q ∧
        ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧
          ∃ s : PeriodOneHminusOne → Coeff 2,
            AnalyticOnNhd ℂ s U ∧ s q = v ∧
              ∀ r ∈ U, periodOneShiftedMiura m (s r) = r := by
  let R : ℝ := 4*B+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hlim : Tendsto (fun m => ‖periodOneMassKernel m‖*R) atTop (𝓝 0) := by
    simpa only [norm_zero,zero_mul] using tendsto_periodOneMassKernel_zero.norm.mul_const R
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4)))
  refine ⟨M,?_⟩
  intro m hm q hq
  have hy : ‖periodOneMassInverse m q‖ ≤ R/2 :=
    (norm_periodOneMassInverse_le m q).trans (by dsimp [R]; linarith)
  exact ComplexAnalysis.exists_analytic_right_inverse_of_small_quadratic
    (periodOneMassInverse m) (periodOneMassInverse_injective m) (periodOneShiftedMiura m)
    (periodOneResolvedProduct m) (periodOneMassInverse_shiftedMiura m)
    (norm_nonneg _) hR (norm_periodOneResolvedProduct_le m) (hM m hm).le q hy

/-- Every complex H^-1 potential has an actual local analytic shifted Miura lift into L2. -/
theorem exists_periodOneMiuraChart (q : PeriodOneHminusOne) :
    ∃ m : ℕ, ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧
      ∃ s : PeriodOneHminusOne → Coeff 2,
        AnalyticOnNhd ℂ s U ∧ ‖s q‖ ≤ 4*‖q‖+1 ∧
          ∀ r ∈ U, periodOneShiftedMiura m (s r) = r := by
  obtain ⟨M,hM⟩ := exists_periodOneMiuraCharts_on_bounded_ball (norm_nonneg q)
  obtain ⟨v,hv,_,U,hU,hq,s,hs,hsv,hsolve⟩ := hM M le_rfl q le_rfl
  exact ⟨M,U,hU,hq,s,hs,by simpa only [hsv] using hv,hsolve⟩

end NLS
