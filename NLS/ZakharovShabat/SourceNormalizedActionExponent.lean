import NLS.ZakharovShabat.SourceNormalizedActionRootAnalytic
import NLS.ZakharovShabat.SourceActionExponentDifferential
import NLS.ZakharovShabat.SourceAngularEtaPhaseExponent
import NLS.ZakharovShabat.SourceOpenGapDensity

/-! # Exponent compatibility of normalized actions through closed gaps

The action factorization identifies the normalized factors on open
gaps. Real open-gap density and continuity identify their values at
closed gaps as well, and hence identify the principal action roots.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem sourceNormalizedActionComplexExtension_real_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (φ : realTypeSourceSubmodule p) :
    sourceNormalizedActionComplexExtension hp hp1 n φ.val =
      sourceNormalizedActionComplexExtension hq hq1 n (CoeffPair.exponentInclusion hpq φ.val) := by
  let F := sourceNormalizedActionComplexExtension hp hp1 n
  let G := sourceNormalizedActionComplexExtension hq hq1 n
  have hc : Continuous (fun ψ : realTypeSourceSubmodule p => F ψ.val - G (CoeffPair.exponentInclusion hpq ψ.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((differentiableAt_sourceNormalizedActionComplexExtension_of_realType hp hp1 ψ.val ψ.property n).continuousAt.sub
      ((differentiableAt_sourceNormalizedActionComplexExtension_of_realType hq hq1 (CoeffPair.exponentInclusion hpq ψ.val)
        (realTypeSourceExponentInclusion hpq ψ).property n).continuousAt.comp
          (CoeffPair.exponentInclusion hpq).continuous.continuousAt)).comp continuous_subtype_val.continuousAt
  apply sub_eq_zero.mp
  exact eq_of_continuousOn_of_sourceFiniteOpenGaps hp hp1 {n} isOpen_univ hc.continuousOn 0
    (fun ψ _ hψ => by
      have hgap := hψ n (by simp)
      change canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n ≠ 0 at hgap
      obtain ⟨U,_,hU,_,hF⟩ := exists_local_sourceNormalizedAction_analytic_factor hp hp1 ψ.val ψ.property n
      obtain ⟨V,_,hV,_,hG⟩ := exists_local_sourceNormalizedAction_analytic_factor hq hq1
        (CoeffPair.exponentInclusion hpq ψ.val) (realTypeSourceExponentInclusion hpq ψ).property n
      have heq := sourceComplexAction_real_exponent hp hq hp1 hq1 hpq n ψ
      rw [hF ψ.val hU,hG _ hV] at heq
      simp only [sourcePeriodicGapDisplacement_apply,
        ← canonicalPeriodicGap_source_exponent hp hq hp1 hq1 hpq ψ.val n] at heq
      exact sub_eq_zero.mpr (mul_left_cancel₀ (pow_ne_zero 2 hgap) heq)) φ (mem_univ _)

theorem sourceNormalizedActionRoot_real_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (φ : realTypeSourceSubmodule p) :
    sourceNormalizedActionRoot hp hp1 n φ.val =
      sourceNormalizedActionRoot hq hq1 n (CoeffPair.exponentInclusion hpq φ.val) := by
  unfold sourceNormalizedActionRoot
  rw [sourceNormalizedActionComplexExtension_real_exponent hp hq hp1 hq1 hpq n φ]

end NLS.ZakharovShabat
