import NLS.SequenceSpaces.NonnegativeActionOverlap

/-! # Gluing analytic maps from nonnegative action data

A family of analytic maps on balls with nonnegative centers glues as soon
as the maps agree on the nonnegative part of each overlap. The union domain
depends only on the balls, so the same domain can serve different target norms.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Local analytic action maps glue uniquely on the union of their balls.
Compatibility need only be checked on nonnegative real actions. -/
theorem exists_analyticOnNhd_gluing_nonnegativeActions (hp : p ≠ ⊤)
    {ι : Type*} (a : ι → Coeff q) (r : ι → ℝ) (f : ι → Coeff q → F)
    (ha : ∀ i, a i ∈ nonnegativeLocus q)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (ball (a i) (r i)))
    (he : ∀ i j c, c ∈ ball (a i) (r i) ∩ ball (a j) (r j) →
      c ∈ nonnegativeLocus q → f i c = f j c) :
    ∃ G : Coeff q → F,
      AnalyticOnNhd ℂ G (⋃ i, ball (a i) (r i)) ∧
      (∀ i, EqOn G (f i) (ball (a i) (r i))) ∧
      (∀ H : Coeff q → F, (∀ i, EqOn H (f i) (ball (a i) (r i))) →
        EqOn H G (⋃ i, ball (a i) (r i))) := by
  classical
  have hcompat (i j : ι) : EqOn (f i) (f j) (ball (a i) (r i) ∩ ball (a j) (r j)) :=
    eqOn_ball_inter_of_nonnegativeActions_agreement hp (f i) (f j) _ _ _ _ (ha i) (ha j)
      (hf i).differentiableOn (hf j).differentiableOn (he i j)
  let G : Coeff q → F := fun c =>
    if hc : ∃ i, c ∈ ball (a i) (r i) then f hc.choose c else 0
  have hG (i : ι) : EqOn G (f i) (ball (a i) (r i)) := by
    intro c hc
    have hex : ∃ j, c ∈ ball (a j) (r j) := ⟨i, hc⟩
    dsimp [G]
    rw [dif_pos hex]
    exact hcompat hex.choose i ⟨hex.choose_spec, hc⟩
  refine ⟨G, ?_, hG, ?_⟩
  · intro c hc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    apply (hf i c hi).congr
    filter_upwards [isOpen_ball.mem_nhds hi] with b hb
    exact (hG i hb).symm
  · intro H hH c hc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    exact (hH i hi).trans (hG i hi).symm

end NLS.Coeff
