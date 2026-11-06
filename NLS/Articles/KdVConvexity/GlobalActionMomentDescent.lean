import NLS.Articles.KdVConvexity.ActionMomentNormalization
import NLS.Articles.KdVConvexity.ArnoldConeMomentGerms
import NLS.Articles.KdVConvexity.LocalCubicPairCharts
import NLS.Articles.KdVConvexity.GlobalArnoldSurjectivity
import NLS.Articles.KdVConvexity.GlobalArnoldActionFibers
import NLS.SequenceSpaces.LocalAtlasActionFamilyDescent

/-! # Global analytic descent of the actual cubic Hill moments to the action cone -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV NLS.Articles.KdVKdV2Frequencies

theorem exists_normalized_cubic_action_family
    (ΩI : Set PeriodOneHminusOne) (hΩI : {q | IsRealPeriodOneHminusOne q} ⊆ ΩI)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I ΩI)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0) :
    ∃ S : ArnoldConeSourceFamily I, ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1 ⊆ V ∧
      (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      (∀ n a, G n a.val = S.scaledCubicMoment n a) ∧
      ∀ b ∈ V, ∃ T : Set (Coeff 1), IsOpen T ∧ b ∈ T ∧ T ⊆ V ∧
        ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ T, ∀ n ∉ s,
          ‖G n c‖ ≤ C*‖normalizedRawActionCoordinate n c‖^2 := by
  classical
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  obtain ⟨S⟩ := nonempty_ArnoldConeSourceFamily ΩI hΩI I hI hrec
  obtain ⟨V,G,hV,hcone,hG,hGrec,hbound⟩ :=
    Coeff.exists_global_scalar_action_family_of_local_real_germs S.scaledCubicMoment
      normalizedRawActionCoordinate (ArnoldConeSourceFamily.localCubicGerms D ΩI hΩI I hI hrec S)
  exact ⟨S,V,G,hV,hcone,hG,hGrec,hbound⟩

/-- Independent ACTUAL local inverse charts descend and glue the cubic
moments near the entire nonnegative weighted action cone, preserving the
uniform local complex quadratic tail bounds and all real physical values. -/
theorem global_cubic_moment_action_descent
    (ΩI : Set PeriodOneHminusOne) (hΩI : {q | IsRealPeriodOneHminusOne q} ⊆ ΩI)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I ΩI)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (hpos : ∀ q, IsRealPeriodOneHminusOne q → I q ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1) :
    ∃ U : Set BaseActionSpace, ∃ R : ℕ+ → BaseActionSpace → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U ∧
      (∀ n, AnalyticOnNhd ℂ (R n) U) ∧
      (∀ q (hr : IsRealPeriodOneHminusOne q), q.val 0 = 0 → ∀ n,
        R n (I q) = hillHminusRealGapCubicContourMoment q hr n) ∧
      ∀ b ∈ U, ∃ T : Set BaseActionSpace, IsOpen T ∧ b ∈ T ∧ T ⊆ U ∧
        ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ T, ∀ n ∉ s,
          ‖weightedContourTerm R n c‖ ≤ C*‖c.val (actionIndexEquiv.symm n)‖^2 := by
  obtain ⟨S,V,G,hV,hcone,hG,hGrec,hbound⟩ :=
    exists_normalized_cubic_action_family ΩI hΩI I hI hrec
  refine ⟨baseActionNormalization ⁻¹' V,unscaledCubicActionFamily G,?_⟩
  have hJ (n : ℕ+) (b : BaseActionSpace) : normalizedRawActionCoordinate n (baseActionNormalization b) =
      b.val (actionIndexEquiv.symm n) := by
    unfold normalizedRawActionCoordinate
    rw [baseActionNormalization.symm_apply_apply]
  exact NLS.ComplexAnalysis.scalarFamily_div_properties_preimage baseActionNormalization
    cubicContourScale cubicContourScale_ne_zero G normalizedRawActionCoordinate
    (fun n b => b.val (actionIndexEquiv.symm n)) hJ V hV
    (WeightedCoeff.nonnegativeLocus baseActionWeight 1) (Coeff.nonnegativeLocus 1)
    (fun b hb => (WeightedCoeff.mem_nonnegativeLocus_iff baseActionWeight 1 b).mp hb)
    hcone hG hbound _ (ArnoldConeSourceFamily.unscaledCubicRecovery I S hrec hpos G hGrec)

end NLS.Articles.KdVConvexity
