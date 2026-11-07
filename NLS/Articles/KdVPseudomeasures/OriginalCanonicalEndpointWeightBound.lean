import NLS.Articles.KdVPseudomeasures.OriginalUniformHighSpectralCompatibility
import NLS.Articles.KdVPseudomeasures.SpectralInverseRestriction
import NLS.Articles.KdVPseudomeasures.SpectralWeightedGaps
import NLS.Articles.KdVPseudomeasures.WeightedComplexMidpoints
import NLS.KdV.HillCanonicalCartesianWeightContinuity
import NLS.Topology.FiniteContinuousUpperBound

/-! A uniform endpoint bound for the ACTUAL intrinsic energy weight.
The complex original norm ball and one native neighborhood precede ALL
positive indices. The finite central block is bounded by continuity;
the entire high tail uses the actual original Theorem 2.1 quantities. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem exists_uniform_source_gap_midpoint_bound (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ n : ℕ+,
        Weight.sobolev (-r) (n:ℤ) *
          (‖sourceComplexCanonicalGapValues r hr q (n:ℤ)‖+‖sourceComplexDirichletMidpoint r hr q hp n‖) ≤ C := by
  obtain ⟨CG,hCG,hG⟩ := (sourceTheorem2_1_i SpectralWeight.one r hr).2 R
  obtain ⟨CM,hCM,hM⟩ := (sourceTheorem2_1_ii SpectralWeight.one r hr).2 R
  refine ⟨CG+CM,add_nonneg hCG hCM,?_⟩
  intro q hq hp n
  let Q := sourceUnitWeightEquiv r q
  have hQ : ‖Q‖ ≤ R := by simpa only [Q,LinearIsometryEquiv.norm_map] using hq
  have hforget : sourceForgetWeight SpectralWeight.one r Q=q := by
    rw [sourceForgetUnitWeight_eq]
    exact (sourceUnitWeightEquiv r).symm_apply_apply q
  have hperiod : IsPeriodicDistribution 1 Q.val.toTempered := by
    simpa only [Q,sourceUnitWeightEquiv_val] using hp
  have hg := (le_div_iff₀ ((SpectralWeight.one.negativeSobolev r).positive (n:ℤ))).mp
    (WeightedCoeff.norm_apply_le _ _ (sourceWeightedCanonicalGaps SpectralWeight.one r hr Q) (n:ℤ))
  rw [sourceWeightedCanonicalGaps_apply,sourceWeightedCanonicalGapValues,hforget] at hg
  have hm := (le_div_iff₀ ((SpectralWeight.one.negativeSobolev r).positive (n:ℤ))).mp
    (WeightedCoeff.norm_apply_le _ _ (sourceWeightedDirichletMidpoints SpectralWeight.one r hr Q hperiod) (n:ℤ))
  simp only [sourceWeightedDirichletMidpoints_nat_apply,hforget] at hm
  simp only [SpectralWeight.negativeSobolev_eq_product,SpectralWeight.one_apply,one_mul] at hg hm
  have hgb := hg.trans (hG Q hQ)
  have hmb := hm.trans (hM Q hQ hperiod)
  nlinarith

theorem exists_local_uniform_canonical_endpoint_weight_bound
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (a : PeriodOneHminusOne) (har : IsRealPeriodOneHminusOne a) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ a ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ _hp : IsPeriodicDistribution 1 q.val.toTempered, sourceNativePeriodOneCLM r hr q ∈ U →
      ∀ n : ℕ+, Weight.sobolev (-r) (n:ℤ) *
        hillHminusCanonicalCartesianWeight n (sourceNativePeriodOneCLM r hr q) ≤ C := by
  obtain ⟨N,V,_,hV,haV,hcompare⟩ := exists_uniform_original_high_canonical_weight_comparison r hr R a har
  obtain ⟨CT,hCT,hT⟩ := exists_uniform_source_gap_midpoint_bound r hr R
  let f (j : ℕ) (q : PeriodOneHminusOne) : ℝ :=
    Weight.sobolev (-r) ((j+1:ℕ):ℤ)*hillHminusCanonicalCartesianWeight ⟨j+1,by omega⟩ q
  obtain ⟨W,hW,haW,CH,hCH,hH⟩ := NLS.Topology.exists_open_finite_continuous_upper_bound
    (Finset.range N) f a (fun j _ => continuousAt_const.mul
      (continuousAt_hillHminusCanonicalCartesianWeight_real ⟨j+1,by omega⟩ a har))
  refine ⟨V ∩ W,hV.inter hW,⟨haV,haW⟩,max CH CT,hCH.trans (le_max_left _ _),?_⟩
  intro q hq hp hqU n
  by_cases hn : N ≤ (n:ℕ)
  · rw [hcompare q hq hp hqU.1 n hn]
    exact (hT q hq hp n).trans (le_max_right _ _)
  · have hj : (n:ℕ)-1 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have he : (n:ℕ)-1+1=(n:ℕ) := Nat.sub_add_cancel (Nat.succ_le_of_lt n.pos)
    have h := hH _ hqU.2 _ hj
    dsimp only [f] at h
    have hpn : (⟨(n:ℕ)-1+1,by omega⟩ : ℕ+)=n := Subtype.ext he
    rw [hpn,he] at h
    exact h.trans (le_max_left CH CT)

end NLS.Articles.KdVPseudomeasures
