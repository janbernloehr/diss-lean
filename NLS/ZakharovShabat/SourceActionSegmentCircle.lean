import NLS.ZakharovShabat.SourceActionCoefficientCircle

/-! # Action circles valid along every interpolation segment

Bounded coefficient convergence persists uniformly along the real source
segments. The common action-circle construction therefore keeps its entire
boundary in the canonical-root domain throughout each eventual segment.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- First-component coefficient limits hold uniformly along the full segments. -/
theorem tendsto_source_segment_fst {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p)
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n))) (n : ℤ) :
    Tendsto (fun t : α × Icc (0 : ℝ) 1 =>
      (BoundedSegmentLimits.segment ψ (φ t.1) t.2).fst n) (l ×ˢ ⊤) (𝓝 (ψ.fst n)) := by
  let F : CoeffPair p →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
    ((ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp (CoeffPair.toMax p).toContinuousLinearMap)
  exact BoundedSegmentLimits.tendsto_coordinate_segment φ ψ F.toLinearMap (ht n)

/-- The second component has the same uniform segment limit. -/
theorem tendsto_source_segment_snd {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p)
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n))) (n : ℤ) :
    Tendsto (fun t : α × Icc (0 : ℝ) 1 =>
      (BoundedSegmentLimits.segment ψ (φ t.1) t.2).snd n) (l ×ˢ ⊤) (𝓝 (ψ.snd n)) := by
  let F : CoeffPair p →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
    ((ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp (CoeffPair.toMax p).toContinuousLinearMap)
  exact BoundedSegmentLimits.tendsto_coordinate_segment φ ψ F.toLinearMap (ht n)

/-- One constructed action circle avoids all cuts along every eventual
interpolation segment, and computes the original indexed endpoint actions. -/
theorem exists_source_actionCircle_along_segments_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax p (φ k))) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n))) (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ ∧
      sourceRealAction hp hp1 ψ hψ n = sourceActionCircle hp hp1 ψ c R ∧
      ∀ᶠ k in l, (∀ t ∈ Icc (0 : ℝ) 1, sphere c R ⊆
        sourceCanonicalRootDomain hp hp1 (BoundedSegmentLimits.segment ψ (φ k) t)) ∧
        sourceRealAction hp hp1 (φ k) (hφ k) n = sourceActionCircle hp hp1 (φ k) c R := by
  let a : α × Icc (0 : ℝ) 1 → CoeffPair p := fun t => BoundedSegmentLimits.segment ψ (φ t.1) t.2
  have hreal (t : α × Icc (0 : ℝ) 1) : IsRealType (CoeffPair.toMax p (a t)) :=
    isRealType_source_segment (φ t.1) ψ (hφ t.1) hψ t.2
  obtain ⟨c,R,hR,_,hlim,he⟩ := exists_source_actionCircle_of_bounded_coefficientwise hp hp1 a ψ
    (BoundedSegmentLimits.bounded_range_segment φ ψ hb) hreal hψ (tendsto_source_segment_fst φ ψ ht) n
  refine ⟨c,R,hR,sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hlim.1 hlim.2.1,hlim.2.2,?_⟩
  rw [← principal_univ,eventually_prod_principal_iff] at he
  filter_upwards [he] with k hk
  constructor
  · intro t ht'
    have h := hk ⟨t,ht'⟩ (mem_univ _)
    exact sourceCanonicalRootDomain_of_enclosingCircle hp hp1 _ n c R h.1 h.2.1
  · simpa only [a,BoundedSegmentLimits.segment_one] using (hk ⟨1,by simp⟩ (mem_univ _)).2.2

end NLS.ZakharovShabat
