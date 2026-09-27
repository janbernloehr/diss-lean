import NLS.ZakharovShabat.SourceNormalizedActionTwoExponentDecomposition
import NLS.ZakharovShabat.SourceNormalizedActionRootSequenceSpace

/-!
# Exact two-exponent asymptotics for the normalized-action root

The principal square root satisfies `‖√z - 1‖ ≤ ‖z - 1‖`.
Together with the exact two-exponent decomposition of the normalized
action, this gives pointwise majorants for the root deviation and
hence an exact `ℓq + ℓ^(p/2)` decomposition with locally uniform
component norm bounds.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For every finite `q > 1`, the principal root deviation is an
exact sum of `ℓq` and `ℓ^(p/2)` components near a real-type source,
each with a locally uniform norm bound. -/
theorem exists_local_sourceNormalizedActionRootDeviation_twoExponentDecomposition
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
        ∃ Rq : Coeff q, ∃ Rg : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ,
            Rq n+Rg n = sourceNormalizedActionRootDeviation hp hp1 ψ n) ∧
          ‖Rq‖ ≤ Lq ∧ ‖Rg‖ ≤ Lg := by
  obtain ⟨V,hVopen,hφV,Lq,Lg,hdecomp⟩ :=
    exists_local_sourceNormalizedActionDeviation_twoExponentDecomposition_allQ
      hp hp1 hq1 hq φ hreal
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hr : 0 < ENNReal.ofReal (p.toReal/2) :=
    ENNReal.ofReal_pos.mpr (half_pos hpr)
  refine ⟨V,hVopen,hφV,Lq,Lg,?_⟩
  intro ψ hψ
  obtain ⟨Aq,Ag,hA,hAq,hAg⟩ := hdecomp ψ hψ
  have hpoint (n : ℤ) :
      ‖sourceNormalizedActionRootDeviation hp hp1 ψ n‖ ≤
        ‖Aq n‖+‖Ag n‖ := by
    calc
      ‖sourceNormalizedActionRootDeviation hp hp1 ψ n‖ ≤
          ‖sourceNormalizedActionDeviation hp hp1 ψ n‖ := by
        simpa only [sourceNormalizedActionRootDeviation,sourceNormalizedActionRoot,
          sourceNormalizedActionDeviation] using
          norm_sqrt_sub_one_le
            (4 * sourceNormalizedActionComplexExtension hp hp1 n ψ)
      _ = ‖Aq n+Ag n‖ := by rw [hA n]
      _ ≤ ‖Aq n‖+‖Ag n‖ := norm_add_le _ _
  obtain ⟨Rq,Rg,hR,hRq,hRg⟩ :=
    Coeff.exists_coeff_decomposition_of_twoSequenceMajorants hr
      (sourceNormalizedActionRootDeviation hp hp1 ψ) Aq Ag hpoint
  exact ⟨Rq,Rg,hR,hRq.trans hAq,hRg.trans hAg⟩

end NLS.ZakharovShabat
