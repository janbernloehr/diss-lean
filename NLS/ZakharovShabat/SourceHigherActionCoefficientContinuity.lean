import NLS.ZakharovShabat.SourceActionCoefficientContinuity
import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic

/-! Actual indexed higher actions preserve bounded coefficient limits.
The spectral power is retained at every natural level; common contours
are constructed, including at collapsed gaps. -/
noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem tendsto_sourceHigherActionCircle_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair 2) (ψ : CoeffPair 2) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax 2 (φ k))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) ψ)
    (hseg : ∀ᶠ k in l, ∀ t ∈ Icc (0 : ℝ) 1, sphere c R ⊆
      sourceCanonicalRootDomain (by simp) (by norm_num) (BoundedSegmentLimits.segment ψ (φ k) t))
    (m : ℕ) :
    Tendsto (fun k => sourceHigherActionCircle (by simp) (by norm_num) (φ k) c R m) l
      (𝓝 (sourceHigherActionCircle (by simp) (by norm_num) ψ c R m)) := by
  have hq := tendstoUniformlyOn_sourceCriticalRootRatio_of_bounded_coefficientwise
    φ ψ hb hφ hψ ht (sphere c R) (isCompact_sphere c R) hc hseg
  have hp : TendstoUniformlyOn (fun _ : α => fun z : ℂ => z^(m+1))
      (fun z => z^(m+1)) l (sphere c R) := by
    intro U hU
    exact Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU
  have hcq := (sourceCriticalRootRatio_analyticOnNhd (by simp) (by norm_num) ψ).continuousOn.mono hc
  have hw := hp.tendstoLocallyUniformlyOn.mul₀ hq.tendstoLocallyUniformlyOn (continuousOn_id.pow (m+1)) hcq
  have hu : TendstoUniformlyOn (fun k z => z^(m+1)*sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,φ k))
      (fun z => z^(m+1)*sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,ψ)) l (sphere c R) := by
    simpa only [Pi.mul_apply] using!
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere c R)).mp hw
  have hcont : ∀ᶠ k in l, ContinuousOn
      (fun z => z^(m+1)*sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,φ k)) (sphere c R) := by
    filter_upwards [hseg] with k hk
    have hdomain : sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (φ k) := by
      simpa only [BoundedSegmentLimits.segment_one] using hk 1 (by simp)
    exact (continuousOn_id.pow (m+1)).mul
      ((sourceCriticalRootRatio_analyticOnNhd (by simp) (by norm_num) (φ k)).continuousOn.mono hdomain)
  exact (hu.tendsto_circleIntegral_of_continuousOn hR hcont).const_mul (((m+1:ℂ)*(Real.pi:ℂ))⁻¹)

theorem sourceIndexedHigherAction_eq_enclosingCircle (ψ : CoeffPair 2)
    (hψ : IsRealType (CoeffPair.toMax 2 ψ)) (n : ℤ) (m : ℕ) (c : ℂ) (R : ℝ)
    (hc : c.im=0) (hR : 0 < R)
    (hgap : sourcePeriodicSegment (by simp) (by norm_num) ψ n ⊆ ball c R)
    (homitted : closedBall c R ⊆ sourceStandardRootOmittedDomain (by simp) (by norm_num) ψ n) :
    sourceIndexedHigherAction (by simp) (by norm_num) n m ψ=
      sourceHigherActionCircle (by simp) (by norm_num) ψ c R m := by
  rw [sourceIndexedHigherAction_eq_real (by simp) (by norm_num) ⟨ψ,hψ⟩ n m]
  exact (sourceHigherActionCircle_eq_real_of_realCentered_enclosingCircle (by simp) (by norm_num)
    ⟨ψ,hψ⟩ n m c R hc hR hgap homitted).symm

theorem tendsto_sourceIndexedHigherAction_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair 2) (ψ : CoeffPair 2) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax 2 (φ k))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n))) (n : ℤ) (m : ℕ) :
    Tendsto (fun k => sourceIndexedHigherAction (by simp) (by norm_num) n m (φ k)) l
      (𝓝 (sourceIndexedHigherAction (by simp) (by norm_num) n m ψ)) := by
  let a : α × Icc (0:ℝ) 1 → CoeffPair 2 := fun t => BoundedSegmentLimits.segment ψ (φ t.1) t.2
  have ha (t : α × Icc (0:ℝ) 1) : IsRealType (CoeffPair.toMax 2 (a t)) :=
    isRealType_source_segment (φ t.1) ψ (hφ t.1) hψ t.2
  obtain ⟨c,R,hR,hc,hlim,he⟩ := exists_source_actionCircle_of_bounded_coefficientwise
    (by simp) (by norm_num) a ψ (BoundedSegmentLimits.bounded_range_segment φ ψ hb) ha hψ
    (tendsto_source_segment_fst φ ψ ht) n
  have hroot : sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) ψ :=
    sourceCanonicalRootDomain_of_enclosingCircle (by simp) (by norm_num) ψ n c R hlim.1 hlim.2.1
  rw [← principal_univ,eventually_prod_principal_iff] at he
  have hseg : ∀ᶠ k in l, ∀ t ∈ Icc (0:ℝ) 1, sphere c R ⊆
      sourceCanonicalRootDomain (by simp) (by norm_num) (BoundedSegmentLimits.segment ψ (φ k) t) := by
    filter_upwards [he] with k hk
    intro t ht'
    have h := hk ⟨t,ht'⟩ (mem_univ _)
    exact sourceCanonicalRootDomain_of_enclosingCircle (by simp) (by norm_num) _ n c R h.1 h.2.1
  rw [sourceIndexedHigherAction_eq_enclosingCircle ψ hψ n m c R hc hR hlim.1 hlim.2.1]
  apply (tendsto_sourceHigherActionCircle_of_bounded_coefficientwise φ ψ hb hφ hψ ht c R hR.le hroot hseg m).congr'
  filter_upwards [he] with k hk
  have h := hk ⟨1,by simp⟩ (mem_univ _)
  simp only [a,BoundedSegmentLimits.segment_one] at h
  exact (sourceIndexedHigherAction_eq_enclosingCircle (φ k) (hφ k) n m c R hc hR h.1 h.2.1).symm

end NLS.ZakharovShabat
