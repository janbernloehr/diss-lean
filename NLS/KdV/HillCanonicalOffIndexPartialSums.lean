import NLS.KdV.HillCanonicalOffIndexAbsoluteSum
import NLS.KdV.HillOffIndexUniformSeries

/-! Literal finite partial sums of the intrinsic ACTUAL correction.
ONE full complex patch ball identifies all terms, partial sums and
the total correction BEFORE ALL numerator and selected indices. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusOffIndexAbelianPartialSum (n : ℕ+) (N : ℕ) (q : PeriodOneHminusOne) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N:ℤ)) N, positiveScalarExtension (hillHminusOffIndexAbelianTerm n q) k

theorem analyticOnNhd_hillHminusOffIndexAbelianTerm (n m : ℕ+) :
    AnalyticOnNhd ℂ (fun q => hillHminusOffIndexAbelianTerm n q m) hillHminusPhysicalAbelianDomain := by
  by_cases hmn : m = n
  · simp only [hillHminusOffIndexAbelianTerm,if_pos hmn]
    exact analyticOnNhd_const
  · simp only [hillHminusOffIndexAbelianTerm,if_neg hmn]
    exact analyticOnNhd_hillHminusPhysicalOffIndexAbelianValue n m hmn

theorem analyticOnNhd_hillHminusOffIndexAbelianPartialSum (n : ℕ+) (N : ℕ) :
    AnalyticOnNhd ℂ (hillHminusOffIndexAbelianPartialSum n N) hillHminusPhysicalAbelianDomain := by
  intro q hq
  apply Finset.analyticAt_fun_sum
  intro k _
  by_cases hk : k ∈ range positiveEmbedding
  · obtain ⟨m,rfl⟩ := hk
    change AnalyticAt ℂ (fun a => positiveScalarExtension (hillHminusOffIndexAbelianTerm n a) ((m:ℕ):ℤ)) q
    simpa only [positiveScalarExtension_apply] using analyticOnNhd_hillHminusOffIndexAbelianTerm n m q hq
  · have he (a : PeriodOneHminusOne) : positiveScalarExtension (hillHminusOffIndexAbelianTerm n a) k = 0 :=
      positiveScalarExtension_zero_of_not_mem_range _ k hk
    simp only [he]
    exact analyticAt_const

theorem exists_common_offIndex_correction_patch_ball (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ P.physicalDirichletSource ∩ hillHminusPhysicalAbelianDomain ∧
      ∀ n : ℕ+, ∀ a ∈ ball q r,
        hillHminusOffIndexAbelianTerm n a = P.physicalOffIndexAbelianTerm n a ∧
        (∀ N : ℕ, hillHminusOffIndexAbelianPartialSum n N a = P.physicalOffIndexAbelianPartialSum n N a) ∧
        hillHminusOffIndexAbelianCorrection n a = P.physicalOffIndexAbelianCorrection n a := by
  obtain ⟨r,hrpos,hball,heq⟩ := exists_common_canonical_physical_Abelian_patch_ball P q hq hr
  refine ⟨r,hrpos,hball,?_⟩
  intro n a ha
  have ht : hillHminusOffIndexAbelianTerm n a = P.physicalOffIndexAbelianTerm n a := by
    funext m
    by_cases hmn : m = n
    · simp only [hillHminusOffIndexAbelianTerm,HillProductEquationPatch.physicalOffIndexAbelianTerm,if_pos hmn]
    · simp only [hillHminusOffIndexAbelianTerm,HillProductEquationPatch.physicalOffIndexAbelianTerm,if_neg hmn,
        heq n m hmn a ha]
  refine ⟨ht,?_,?_⟩
  · intro N
    simp only [hillHminusOffIndexAbelianPartialSum,HillProductEquationPatch.physicalOffIndexAbelianPartialSum,ht]
  · simp only [hillHminusOffIndexAbelianCorrection,HillProductEquationPatch.physicalOffIndexAbelianCorrection,ht]

end NLS.KdV
