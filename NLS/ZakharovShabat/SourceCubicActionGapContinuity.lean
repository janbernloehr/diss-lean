import NLS.ZakharovShabat.SourceCubicActionGapBudget
import NLS.ZakharovShabat.SourceNormalizedActionComplexExtension
import NLS.ZakharovShabat.SourcePeriodicMidpointGapContinuity

/-! # Removal of the apparent singularity in the cubic action-gap correction -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Factoring the actual action removes the denominator, also at a collapsed gap. -/
theorem sourceCubicActionGapTerm_eq_normalized (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hf : sourceComplexAction hp hp1 n ψ = (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*
      sourceNormalizedActionComplexExtension hp hp1 n ψ) :
    sourceCubicActionGapTerm hp hp1 ψ n =
      ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^4*
        ‖sourceNormalizedActionComplexExtension hp hp1 n ψ‖^3 := by
  unfold sourceCubicActionGapTerm
  rw [hf,← sourcePeriodicGapDisplacement_apply,norm_mul,norm_pow,mul_pow]
  by_cases hg : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · simp only [hg,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),
      zero_pow (by norm_num : (3:ℕ) ≠ 0),zero_pow (by norm_num : (4:ℕ) ≠ 0),zero_mul,zero_div]
  · have hn : ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ ≠ 0 := norm_ne_zero_iff.mpr hg
    field_simp

/-- Each correction term is continuous through collapsed gaps in the original source topology. -/
theorem continuousAt_sourceCubicActionGapTerm_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ContinuousAt (fun ψ => sourceCubicActionGapTerm hp hp1 ψ n) φ := by
  obtain ⟨U,hU,hφU,hρ,hfac⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_differentiableOn hp hp1 φ hφ n
  have hgap : ContinuousAt (fun ψ => sourcePeriodicGapDisplacement hp hp1 ψ n) φ := by
    have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ hφ n
    have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ hφ n
    simpa only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,Pi.sub_apply] using! hR.sub hL
  have hc := (hgap.norm.pow 4).mul
    (((hρ φ hφU).differentiableAt (hU.mem_nhds hφU)).continuousAt.norm.pow 3)
  apply hc.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hφU] with ψ hψ
  exact sourceCubicActionGapTerm_eq_normalized hp hp1 ψ n (hfac ψ hψ)

end NLS.ZakharovShabat
