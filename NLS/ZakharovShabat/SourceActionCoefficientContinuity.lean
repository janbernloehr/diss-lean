import NLS.ZakharovShabat.SourceCanonicalRootCoefficientContinuity
import NLS.ZakharovShabat.SourceDiscriminantDerivativeCoefficientContinuity
import NLS.ComplexAnalysis.UniformInverseCompact

/-! # Actual Hilbert action continuity under bounded coefficient limits

The normalized canonical root and discriminant derivative converge uniformly
on a common circle valid along all source interpolation segments. The root
is bounded away from zero there, so the actual quotient and its weighted
circle integral converge. No contour or open-gap hypothesis is required in
the final theorem for the original indexed real actions.
-/
noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- Uniform convergence of the actual critical-root quotient on compact
sets that avoid all cuts along the eventual source segments. -/
theorem tendstoUniformlyOn_sourceCriticalRootRatio_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (φ : α → CoeffPair 2) (ψ : CoeffPair 2)
    (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax 2 (φ k))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (K : Set ℂ) (hK : IsCompact K)
    (hKψ : K ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) ψ)
    (hseg : ∀ᶠ k in l, ∀ t ∈ Icc (0 : ℝ) 1, K ⊆
      sourceCanonicalRootDomain (by simp) (by norm_num) (BoundedSegmentLimits.segment ψ (φ k) t)) :
    TendstoUniformlyOn (fun k z => sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,φ k))
      (fun z => sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,ψ)) l K := by
  have hr := tendstoUniformlyOn_sourceCanonicalRoot_of_bounded_coefficientwise φ ψ hb hφ hψ ht K hK hKψ hseg
  have hcr := (sourceCanonicalRoot_analyticOnNhd (by simp) (by norm_num) ψ).continuousOn.mono hKψ
  have hne := fun z hz => sourceCanonicalRoot_ne_zero_off_gaps (by simp) (by norm_num) ψ z (hKψ hz)
  have hi := NLS.ComplexAnalysis.tendstoUniformlyOn_inv_of_compact_nonzero hr hK hcr hne
  have hd := tendstoUniformlyOn_sourceDiscriminant_deriv_of_bounded_coefficientwise φ ψ hb ht
    (tendsto_source_snd_of_realType_coefficientwise φ ψ hφ hψ ht) K hK.isBounded
  have hcd := (analyticOnNhd_discriminant_derivative (by simp) (by norm_num)
    (periodOnePotential ψ) (periodOnePotential_mem ψ)).continuousOn.mono (subset_univ K)
  have hprod := hd.tendstoLocallyUniformlyOn.mul₀ hi.tendstoLocallyUniformlyOn hcd (hcr.inv₀ hne)
  simpa only [sourceCriticalRootRatioJoint,div_eq_mul_inv,Pi.mul_apply] using!
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp hprod

/-- The actual action on a fixed admissible circle converges. -/
theorem tendsto_sourceActionCircle_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair 2) (ψ : CoeffPair 2) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax 2 (φ k))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) ψ)
    (hseg : ∀ᶠ k in l, ∀ t ∈ Icc (0 : ℝ) 1, sphere c R ⊆
      sourceCanonicalRootDomain (by simp) (by norm_num) (BoundedSegmentLimits.segment ψ (φ k) t)) :
    Tendsto (fun k => sourceActionCircle (by simp) (by norm_num) (φ k) c R) l
      (𝓝 (sourceActionCircle (by simp) (by norm_num) ψ c R)) := by
  have hq := tendstoUniformlyOn_sourceCriticalRootRatio_of_bounded_coefficientwise
    φ ψ hb hφ hψ ht (sphere c R) (isCompact_sphere c R) hc hseg
  have hid : TendstoUniformlyOn (fun _ : α => id) id l (sphere c R) := by
    intro U hU
    exact Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU
  have hcq := (sourceCriticalRootRatio_analyticOnNhd (by simp) (by norm_num) ψ).continuousOn.mono hc
  have hw := hid.tendstoLocallyUniformlyOn.mul₀ hq.tendstoLocallyUniformlyOn continuousOn_id hcq
  have hu : TendstoUniformlyOn (fun k z => z*sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,φ k))
      (fun z => z*sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,ψ)) l (sphere c R) := by
    simpa only [Pi.mul_apply,id_eq] using!
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere c R)).mp hw
  have hcont : ∀ᶠ k in l, ContinuousOn (fun z => z*sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,φ k)) (sphere c R) := by
    filter_upwards [hseg] with k hk
    have hdomain : sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (φ k) := by
      simpa only [BoundedSegmentLimits.segment_one] using hk 1 (by simp)
    exact continuousOn_id.mul ((sourceCriticalRootRatio_analyticOnNhd (by simp) (by norm_num) (φ k)).continuousOn.mono hdomain)
  exact (hu.tendsto_circleIntegral_of_continuousOn hR hcont).const_mul (Real.pi : ℂ)⁻¹

/-- Every original indexed real Hilbert action is continuous under bounded
coefficient limits, including collapsed gaps. Only first-component limits
are supplied; the common circle and normalized root convergence are proved. -/
theorem tendsto_sourceRealAction_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair 2) (ψ : CoeffPair 2) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax 2 (φ k))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n))) (n : ℤ) :
    Tendsto (fun k => sourceRealAction (by simp) (by norm_num) (φ k) (hφ k) n) l
      (𝓝 (sourceRealAction (by simp) (by norm_num) ψ hψ n)) := by
  obtain ⟨c,R,hR,hc,hlim,he⟩ := exists_source_actionCircle_along_segments_of_bounded_coefficientwise
    (by simp) (by norm_num) φ ψ hb hφ hψ ht n
  rw [hlim]
  apply (tendsto_sourceActionCircle_of_bounded_coefficientwise φ ψ hb hφ hψ ht c R hR.le hc
    (he.mono fun _ hk => hk.1)).congr'
  exact he.mono fun _ hk => hk.2.symm

end NLS.ZakharovShabat
