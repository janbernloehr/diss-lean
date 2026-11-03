import NLS.SequenceSpaces.PeriodOneMiuraConjugation
import NLS.ComplexAnalysis.EquivariantSmallQuadraticInverse

/-! # Actual real-preserving Miura charts on the rough space

The mass is chosen uniformly before the potential on a bounded rough
ball. The complex analytic lift solves the actual distributional equation
and preserves physical realness at every nearby real input.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS

theorem exists_real_periodOneMiuraCharts_on_bounded_ball {B : ℝ} (hB : 0 ≤ B) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ q : PeriodOneHminusOne, ‖q‖ ≤ B →
      periodOneHminusConjugation q = q →
      ∃ v : Coeff 2, ‖v‖ ≤ 3*(4*B+1)/4 ∧ periodOneShiftedMiura m v = q ∧
        periodOneL2Conjugation v = v ∧ ∃ U : Set PeriodOneHminusOne,
          IsOpen U ∧ q ∈ U ∧ ∃ s : PeriodOneHminusOne → Coeff 2,
            AnalyticOnNhd ℂ s U ∧ s q = v ∧
            (∀ r ∈ U, periodOneShiftedMiura m (s r) = r) ∧
            ∀ r ∈ U, periodOneHminusConjugation r = r → periodOneL2Conjugation (s r) = s r := by
  let R : ℝ := 4*B+1
  have hR : 0 < R := by dsimp only [R];positivity
  have hlim : Tendsto (fun m => ‖periodOneMassKernel m‖*R) atTop (𝓝 0) := by
    simpa only [norm_zero,zero_mul] using tendsto_periodOneMassKernel_zero.norm.mul_const R
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4)))
  refine ⟨M,?_⟩
  intro m hm q hq hqreal
  have hy : ‖periodOneMassInverse m q‖ ≤ R/2 :=
    (norm_periodOneMassInverse_le m q).trans (by dsimp only [R];linarith)
  exact ComplexAnalysis.exists_equivariant_analytic_right_inverse_of_small_quadratic
    (periodOneMassInverse m) (periodOneMassInverse_injective m) (periodOneShiftedMiura m)
    (periodOneResolvedProduct m) (periodOneMassInverse_shiftedMiura m)
    (norm_nonneg _) hR (norm_periodOneResolvedProduct_le m) (hM m hm).le
    periodOneL2Conjugation periodOneHminusConjugation norm_periodOneL2Conjugation
    (periodOneResolvedQuadratic_conjugation m) (periodOneMassInverse_conjugation m) q hy hqreal

/-- Every physically real rough potential has a complex analytic actual
Miura lift that remains physically real at every real input in its domain.
The constant energy translation is fixed before those nearby inputs. -/
theorem exists_real_periodOneMiura_energyChart (q : PeriodOneHminusOne)
    (hqreal : periodOneHminusConjugation q = q) :
    ∃ m : ℕ, ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧
      ∃ u : PeriodOneHminusOne → Coeff 2, AnalyticOnNhd ℂ u U ∧
        (∀ r ∈ U, periodOneMiura (u r) = r+
          periodOneL2Inclusion (lp.single 2 0 ((((m : ℝ)+1 : ℝ)/2 : ℂ)^2))) ∧
        ∀ r ∈ U, periodOneHminusConjugation r = r → periodOneL2Conjugation (u r) = u r := by
  obtain ⟨M,hM⟩ := exists_real_periodOneMiuraCharts_on_bounded_ball (norm_nonneg q)
  obtain ⟨v,_,_,_,U,hU,hq,s,hs,_,hsolve,hreal⟩ := hM M le_rfl q le_rfl hqreal
  let c : ℝ := ((M : ℝ)+1)/2
  refine ⟨M,U,hU,hq,(fun r => s r+lp.single 2 0 (c : ℂ)),?_,?_,?_⟩
  · intro r hr
    exact (hs r hr).add analyticAt_const
  · intro r hr
    have he := periodOneMiura_shift M (s r)
    rw [hsolve r hr] at he
    simpa only [c,Complex.ofReal_div,Complex.ofReal_ofNat] using! he
  · intro r hr hrreal
    rw [periodOneL2Conjugation_add,hreal r hr hrreal,periodOneL2Conjugation_single_real]

end NLS
