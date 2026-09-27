import NLS.SequenceSpaces.OnePlus
import NLS.ZakharovShabat.SourceNormalizedActionHolomorphicCommonExponentDomain

/-!
# Simultaneous `ℓ^(1+)` action and root deviations

For `1 < p ≤ 2`, the common-neighborhood estimates assemble the
normalized-action and principal-root deviations as actual sequences
in the intersection of all finite `ℓq` spaces with `q > 1`. Each
canonical `ℓq` projection is locally bounded on the same source
neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The action and principal-root deviations have genuine
`ℓ^(1+)`-valued realizations on one complex source neighborhood.
Every finite `ℓq`, `q > 1`, projection is locally bounded there. -/
theorem exists_local_sourceNormalizedAction_onePlus
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ A R : CoeffPair p → CoeffOnePlus,
        (∀ ψ ∈ V, ∀ n : ℤ,
          (A ψ).1 n = sourceNormalizedActionDeviation hp hp1 ψ n ∧
          (R ψ).1 n = sourceNormalizedActionRootDeviation hp hp1 ψ n) ∧
        ∀ (q : ℝ≥0∞) (_hq1 : 1 < q) (_hq : q ≠ ⊤),
          ∃ Ma Mr : ℝ, ∀ ψ ∈ V,
            ‖CoeffOnePlus.toCoeff q _hq1 _hq (A ψ)‖ ≤ Ma ∧
            ‖CoeffOnePlus.toCoeff q _hq1 _hq (R ψ)‖ ≤ Mr := by
  classical
  obtain ⟨V,hVopen,hφV,hpair⟩ :=
    exists_local_sourceNormalizedAction_and_root_holomorphic_allExponents
      hp hp1 hp2 φ hφ
  have hmemA (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      ∀ (q : ℝ≥0∞), 1 < q → q ≠ ⊤ →
        Memℓp (sourceNormalizedActionDeviation hp hp1 ψ) q := by
    intro q hq1 hq
    obtain ⟨F,G,hcoord,_,_,Ma,Mr,hbounds⟩ :=
      @hpair q ⟨hq1.le⟩ hq1 hq
    have heq : (fun n => F ψ n) =
        sourceNormalizedActionDeviation hp hp1 ψ := by
      funext n
      exact (hcoord ψ hψ n).1
    rw [← heq]
    exact lp.memℓp (F ψ)
  have hmemR (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      ∀ (q : ℝ≥0∞), 1 < q → q ≠ ⊤ →
        Memℓp (sourceNormalizedActionRootDeviation hp hp1 ψ) q := by
    intro q hq1 hq
    obtain ⟨F,G,hcoord,_,_,Ma,Mr,hbounds⟩ :=
      @hpair q ⟨hq1.le⟩ hq1 hq
    have heq : (fun n => G ψ n) =
        sourceNormalizedActionRootDeviation hp hp1 ψ := by
      funext n
      exact (hcoord ψ hψ n).2
    rw [← heq]
    exact lp.memℓp (G ψ)
  let A : CoeffPair p → CoeffOnePlus := fun ψ =>
    if hψ : ψ ∈ V then
      ⟨sourceNormalizedActionDeviation hp hp1 ψ,hmemA ψ hψ⟩ else 0
  let R : CoeffPair p → CoeffOnePlus := fun ψ =>
    if hψ : ψ ∈ V then
      ⟨sourceNormalizedActionRootDeviation hp hp1 ψ,hmemR ψ hψ⟩ else 0
  refine ⟨V,hVopen,hφV,A,R,?_,?_⟩
  · intro ψ hψ n
    simp [A,R,hψ]
  · intro q hq1 hq
    obtain ⟨F,G,hcoord,_,_,Ma,Mr,hbounds⟩ :=
      @hpair q ⟨hq1.le⟩ hq1 hq
    refine ⟨Ma,Mr,?_⟩
    intro ψ hψ
    have hA : CoeffOnePlus.toCoeff q hq1 hq (A ψ) = F ψ := by
      ext n
      simp only [CoeffOnePlus.toCoeff_apply,A,dif_pos hψ]
      exact (hcoord ψ hψ n).1.symm
    have hR : CoeffOnePlus.toCoeff q hq1 hq (R ψ) = G ψ := by
      ext n
      simp only [CoeffOnePlus.toCoeff_apply,R,dif_pos hψ]
      exact (hcoord ψ hψ n).2.symm
    rw [hA,hR]
    exact hbounds ψ hψ

end NLS.ZakharovShabat
