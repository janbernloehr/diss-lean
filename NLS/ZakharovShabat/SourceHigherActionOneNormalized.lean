import NLS.ZakharovShabat.SourceHigherActionOneCircleQuotient
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedPositive
import NLS.ZakharovShabat.SourceIndexedHigherActionReal

/-! # The actual level-two action divided by the squared Dirac gap

The filled quotient is chart-independent and analytic near every real
source, with its exact original indexed-action factorization at complex
collapsed gaps. Its real positivity on a positive spectral interval uses
the real mean-value formula only for real values; no analytic mean-value
point is assumed or constructed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceHigherActionOneNormalized (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) : ℂ :=
  if sourcePeriodicGapDisplacement hp hp1 ψ n = 0 then
    sourceStandardRootMidpoint hp hp1 ψ n*sourceNormalizedActionCollapsedCandidate hp hp1 n ψ
  else sourceIndexedHigherAction hp hp1 n 1 ψ/(sourcePeriodicGapDisplacement hp hp1 ψ n)^2

theorem sourceHigherActionOneNormalized_eq_quotient_of_gap_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n ≠ 0) :
    sourceHigherActionOneNormalized hp hp1 n ψ =
      sourceIndexedHigherAction hp hp1 n 1 ψ/(sourcePeriodicGapDisplacement hp hp1 ψ n)^2 := by
  rw [sourceHigherActionOneNormalized,if_neg hgap]

theorem sourceHigherActionOneNormalized_eq_midpoint_mul_of_gap_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) :
    sourceHigherActionOneNormalized hp hp1 n ψ =
      sourceStandardRootMidpoint hp hp1 ψ n*sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  simp only [sourceHigherActionOneNormalized,sourceNormalizedActionComplexExtension,
    sourceNormalizedActionRealExtension,if_pos hgap]

theorem exists_local_sourceHigherActionOneNormalized
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      AnalyticOnNhd ℂ (sourceHigherActionOneNormalized hp hp1 n) U ∧
      ∀ ψ ∈ U, sourceIndexedHigherAction hp hp1 n 1 ψ =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*sourceHigherActionOneNormalized hp hp1 n ψ := by
  obtain ⟨U,hU,hφU,c,R,_,hQ,hdata⟩ := exists_local_sourceHigherActionOneCircleQuotient hp hp1 φ hφ n
  have heq : EqOn (sourceHigherActionOneNormalized hp hp1 n)
      (sourceHigherActionOneCircleQuotient hp hp1 n c R) U := by
    intro ψ hψ
    by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
    · rw [sourceHigherActionOneNormalized,if_pos hgap]
      exact ((hdata ψ hψ).2 hgap).symm
    · rw [sourceHigherActionOneNormalized,if_neg hgap,(hdata ψ hψ).1]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hgap)
  refine ⟨U,hU,hφU,?_,?_⟩
  · intro ψ hψ
    apply (hQ ψ hψ).congr
    filter_upwards [hU.mem_nhds hψ] with χ hχ
    exact (heq hχ).symm
  · intro ψ hψ
    rw [heq hψ]
    exact (hdata ψ hψ).1

theorem analyticAt_sourceHigherActionOneNormalized_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    AnalyticAt ℂ (sourceHigherActionOneNormalized hp hp1 n) φ := by
  obtain ⟨_,_,hφU,ha,_⟩ := exists_local_sourceHigherActionOneNormalized hp hp1 φ hφ n
  exact ha φ hφU

theorem sourceHigherActionOneNormalized_re_pos_of_left_pos
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hleft : 0 < (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re) :
    0 < (sourceHigherActionOneNormalized hp hp1 n φ.val).re := by
  have hpos := sourceNormalizedActionComplexExtension_re_pos_of_realType hp hp1 n φ.val φ.property
  have him := sourceNormalizedActionComplexExtension_im_eq_zero_of_realType hp hp1 n φ.val φ.property
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0
  · have hord := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _)).2.1 n)
    have hmid : 0 < (sourceStandardRootMidpoint hp hp1 φ.val n).re := by
      let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n
      let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n
      have hs : 0 < l.re+r.re := by
        change 0 < l.re at hleft
        change l.re ≤ r.re at hord
        linarith
      change 0 < ((l+r)/2).re
      have he : ((l+r)/2).re = (l.re+r.re)/2 := by simp
      rw [he]
      exact div_pos hs (by norm_num)
    rw [sourceHigherActionOneNormalized_eq_midpoint_mul_of_gap_zero hp hp1 n φ.val hgap,
      mul_re,him,mul_zero,sub_zero]
    exact mul_pos hmid hpos
  · obtain ⟨ζ,hζ,he⟩ := sourceIndexedHigherAction_eq_power_mul_action hp hp1 φ n 1
    have hζpos : 0 < ζ := hleft.trans_le hζ.1
    have haction : sourceIndexedAction hp hp1 n φ.val = sourceComplexAction hp hp1 n φ.val :=
      (sourceIndexedAction_eq_sourceRealAction hp hp1 n φ.val φ.property).trans
        (sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property).symm
    have hnorm : sourceComplexAction hp hp1 n φ.val/(sourcePeriodicGapDisplacement hp hp1 φ.val n)^2 =
        sourceNormalizedActionComplexExtension hp hp1 n φ.val := by
      simp only [sourceNormalizedActionComplexExtension,sourceNormalizedActionRealExtension,
        if_neg hgap,sourceRawNormalizedAction]
    rw [sourceHigherActionOneNormalized_eq_quotient_of_gap_ne_zero hp hp1 n φ.val hgap,
      he,pow_one,haction,mul_div_assoc,hnorm,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
    exact mul_pos hζpos hpos

theorem exists_local_sourceHigherActionOneNormalized_nonzero_of_left_pos
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hleft : 0 < (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      AnalyticOnNhd ℂ (sourceHigherActionOneNormalized hp hp1 n) U ∧
      ∀ ψ ∈ U, sourceHigherActionOneNormalized hp hp1 n ψ ≠ 0 ∧
        sourceIndexedHigherAction hp hp1 n 1 ψ =
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*sourceHigherActionOneNormalized hp hp1 n ψ := by
  obtain ⟨V,hV,hφV,ha,hfactor⟩ := exists_local_sourceHigherActionOneNormalized hp hp1 φ.val φ.property n
  have hnz : sourceHigherActionOneNormalized hp hp1 n φ.val ≠ 0 := by
    intro he
    have hpos := sourceHigherActionOneNormalized_re_pos_of_left_pos hp hp1 φ n hleft
    rw [he,zero_re] at hpos
    exact lt_irrefl 0 hpos
  let U := V ∩ {ψ | sourceHigherActionOneNormalized hp hp1 n ψ ≠ 0}
  have hU : IsOpen U := ha.continuousOn.isOpen_inter_preimage hV isOpen_compl_singleton
  exact ⟨U,hU,⟨hφV,hnz⟩,ha.mono inter_subset_left,fun ψ hψ => ⟨hψ.2,hfactor ψ hψ.1⟩⟩

end NLS.ZakharovShabat
