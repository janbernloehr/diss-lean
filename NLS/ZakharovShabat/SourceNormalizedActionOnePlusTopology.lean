import NLS.SequenceSpaces.OnePlusTopology
import NLS.ZakharovShabat.SourceNormalizedActionOnePlus

/-!
# Continuity of the `ℓ^(1+)` action and root maps

The projective topology on `CoeffOnePlus` detects continuity through
its Banach-space projections. Since the action and root projections
are Fréchet-holomorphic on one common complex source neighborhood,
their `ℓ^(1+)` realizations are continuous there.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For `1 < p ≤ 2`, the normalized-action and principal-root
deviations are continuous `ℓ^(1+)`-valued maps on one complex source
neighborhood. Every finite-`ℓq` projection remains locally bounded. -/
theorem exists_local_sourceNormalizedAction_onePlus_continuous
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ A R : CoeffPair p → CoeffOnePlus,
        (∀ ψ ∈ V, ∀ n : ℤ,
          (A ψ).1 n = sourceNormalizedActionDeviation hp hp1 ψ n ∧
          (R ψ).1 n = sourceNormalizedActionRootDeviation hp hp1 ψ n) ∧
        ContinuousOn A V ∧ ContinuousOn R V ∧
        ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
          ∃ Ma Mr : ℝ, ∀ ψ ∈ V,
            ‖CoeffOnePlus.toCoeff q hq1 hq (A ψ)‖ ≤ Ma ∧
            ‖CoeffOnePlus.toCoeff q hq1 hq (R ψ)‖ ≤ Mr := by
  obtain ⟨V₁,hV₁open,hφV₁,A,R,hcoords,hbounds⟩ :=
    exists_local_sourceNormalizedAction_onePlus hp hp1 hp2 φ hφ
  obtain ⟨V₂,hV₂open,hφV₂,hpair⟩ :=
    exists_local_sourceNormalizedAction_and_root_holomorphic_allExponents
      hp hp1 hp2 φ hφ
  let V := V₁ ∩ V₂
  have hVopen : IsOpen V := hV₁open.inter hV₂open
  have hAcont : ContinuousOn A V := by
    apply (CoeffOnePlus.continuousOn_iff_projections A V).2
    intro e
    let : Fact (1 ≤ e.1) := ⟨e.2.1.le⟩
    obtain ⟨F,G,hpaircoord,hFdiff,hGdiff,Ma,Mr,hpairbounds⟩ :=
      hpair e.1 e.2.1 e.2.2
    apply (hFdiff.continuousOn.mono inter_subset_right).congr
    intro ψ hψ
    ext n
    rw [CoeffOnePlus.toCoeff_apply]
    exact (hcoords ψ hψ.1 n).1.trans (hpaircoord ψ hψ.2 n).1.symm
  have hRcont : ContinuousOn R V := by
    apply (CoeffOnePlus.continuousOn_iff_projections R V).2
    intro e
    let : Fact (1 ≤ e.1) := ⟨e.2.1.le⟩
    obtain ⟨F,G,hpaircoord,hFdiff,hGdiff,Ma,Mr,hpairbounds⟩ :=
      hpair e.1 e.2.1 e.2.2
    apply (hGdiff.continuousOn.mono inter_subset_right).congr
    intro ψ hψ
    ext n
    rw [CoeffOnePlus.toCoeff_apply]
    exact (hcoords ψ hψ.1 n).2.trans (hpaircoord ψ hψ.2 n).2.symm
  refine ⟨V,hVopen,⟨hφV₁,hφV₂⟩,A,R,?_,hAcont,hRcont,?_⟩
  · intro ψ hψ n
    exact hcoords ψ hψ.1 n
  · intro q hq1 hq
    obtain ⟨Ma,Mr,hbound⟩ := hbounds q hq1 hq
    exact ⟨Ma,Mr,fun ψ hψ => hbound ψ hψ.1⟩

end NLS.ZakharovShabat
