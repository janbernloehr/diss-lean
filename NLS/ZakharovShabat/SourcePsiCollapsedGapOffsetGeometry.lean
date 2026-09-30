import NLS.ZakharovShabat.SourcePsiIsolatingComplexRootAtlas
import NLS.ZakharovShabat.SourcePeriodicMidpointGapContinuity

/-!
# Fixed offset contours near a collapsed reference gap

A real reference midpoint lies strictly inside its assigned disc.
A smaller fixed circle with twice its radius still in that disc
separates every other moving midpoint. Endpoint continuity makes the
selected midpoint displacement and gap small relative to this circle.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourcePeriodicSegment_subset_ball_of_small_midpoint_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ m-c‖ ≤ R/4)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ R/2) :
    sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ m
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  have hl : l = τ-γ/2 := by
    simp only [l,τ,γ,sourcePeriodicGapDisplacement_apply,
      canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hr : r = τ+γ/2 := by
    simp only [r,τ,γ,sourcePeriodicGapDisplacement_apply,
      canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hhalf : ‖γ/2‖ ≤ R/4 := by
    rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    dsimp only [γ]
    linarith
  have hleft : l ∈ ball c R := by
    rw [mem_ball,dist_eq_norm,hl]
    have heq : τ-γ/2-c = (τ-c)-γ/2 := by ring
    rw [heq]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hright : r ∈ ball c R := by
    rw [mem_ball,dist_eq_norm,hr]
    have heq : τ+γ/2-c = (τ-c)+γ/2 := by ring
    rw [heq]
    exact (norm_add_le _ _).trans_lt (by linarith)
  exact (convex_ball c R).segment_subset hleft hright

theorem SourcePsiIsolatingComplexRootAtlas.exists_local_collapsed_gap_offset_circle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
    (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U) (φ : realTypeSourceLocus p)
    (m : ℤ) (hγ : sourcePeriodicGapDisplacement hp hp1 φ.val m = 0) :
    ∃ r : ℝ, 0 < r ∧
      closedBall (sourceStandardRootMidpoint hp hp1 φ.val m) (2*r) ⊆
        sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ A.toSourcePsiComplexRootAtlas.sourceBall φ ∧
        ∀ ψ ∈ V,
          ‖sourceStandardRootMidpoint hp hp1 ψ m-sourceStandardRootMidpoint hp hp1 φ.val m‖ ≤ r/4 ∧
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ r/2 := by
  let B := A.toSourcePsiComplexRootAtlas
  let c := sourceStandardRootMidpoint hp hp1 φ.val m
  have hbase : φ.val ∈ B.sourceBall φ := mem_ball_self (B.localBranch φ).sourceRadius_pos
  have hc : c ∈ sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val φ.val (A.cutoff φ) (A.enlargement φ) m
      (A.clusters φ φ.val hbase m) (sourcePeriodicMidpoint_mem_segment hp hp1 φ.val m)
  obtain ⟨ρ,hρ,hρball⟩ := Metric.isOpen_iff.mp
    (isOpen_sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m) c hc
  let r := ρ/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hclosed : closedBall c (2*r) ⊆
      sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans hρball
  have hmidCont : ContinuousAt (fun ψ : CoeffPair p => sourceStandardRootMidpoint hp hp1 ψ m) φ.val :=
    ((continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ.val φ.property m).add
      (continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ.val φ.property m)).div_const (2 : ℂ)
  have hgapCont : ContinuousAt (fun ψ : CoeffPair p => sourcePeriodicGapDisplacement hp hp1 ψ m) φ.val :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).continuous.continuousAt.comp
      (continuousAt_sourcePeriodicGapDisplacement_of_realType hp hp1 φ.val φ.property)
  obtain ⟨δm,hδm,hmid⟩ := Metric.continuousAt_iff.mp hmidCont (r/4) (by positivity)
  obtain ⟨δg,hδg,hgap⟩ := Metric.continuousAt_iff.mp hgapCont (r/2) (by positivity)
  let δ := min (B.localBranch φ).sourceRadius (min δm δg)
  have hδ : 0 < δ := lt_min (B.localBranch φ).sourceRadius_pos (lt_min hδm hδg)
  refine ⟨r,hr,hclosed,ball φ.val δ,isOpen_ball,mem_ball_self hδ,
    ball_subset_ball (min_le_left _ _),?_⟩
  intro ψ hψ
  have hdψ := mem_ball.mp hψ
  constructor
  · have h := hmid (hdψ.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have hnorm : ‖sourceStandardRootMidpoint hp hp1 ψ m-c‖ < r/4 := by
      simpa only [dist_eq_norm] using h
    exact hnorm.le
  · have h := hgap (hdψ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    rw [hγ,dist_zero_right] at h
    exact h.le

end NLS.ZakharovShabat
