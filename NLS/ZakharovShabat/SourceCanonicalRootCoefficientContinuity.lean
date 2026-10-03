import NLS.ComplexAnalysis.SquareRootPathStability
import NLS.ZakharovShabat.SourceActionSegmentCircle
import NLS.ZakharovShabat.SourceDiscriminantCoefficientContinuity
import NLS.ZakharovShabat.SourceCanonicalRootJointAnalytic
import Mathlib.Topology.MetricSpace.Algebra

/-! # Canonical-root convergence under bounded coefficient limits

Uniform discriminant convergence along real interpolation segments controls
the squares of the canonical roots. Joint analyticity makes each root path
continuous. Its normalization at the limit source fixes its branch, giving
uniform convergence on any compact set kept off all cuts along the segments.
-/
noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The actual canonical branch converges uniformly, with its sign retained,
on a compact set valid throughout every eventual real interpolation segment. -/
theorem tendstoUniformlyOn_sourceCanonicalRoot_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (φ : α → CoeffPair 2) (ψ : CoeffPair 2)
    (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ k, IsRealType (CoeffPair.toMax 2 (φ k))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (K : Set ℂ) (hK : IsCompact K)
    (hKψ : K ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) ψ)
    (hseg : ∀ᶠ k in l, ∀ t ∈ Icc (0 : ℝ) 1, K ⊆
      sourceCanonicalRootDomain (by simp) (by norm_num) (BoundedSegmentLimits.segment ψ (φ k) t)) :
    TendstoUniformlyOn (fun k => sourceCanonicalRoot (by simp) (by norm_num) (φ k))
      (sourceCanonicalRoot (by simp) (by norm_num) ψ) l K := by
  let a : α × Icc (0 : ℝ) 1 → CoeffPair 2 := fun t => BoundedSegmentLimits.segment ψ (φ t.1) t.2
  have ht₂ := tendsto_source_snd_of_realType_coefficientwise φ ψ hφ hψ ht
  have hΔ := tendstoLocallyUniformly_sourceDiscriminant_of_bounded_coefficientwise a ψ
    (BoundedSegmentLimits.bounded_range_segment φ ψ hb)
    (tendsto_source_segment_fst φ ψ ht) (tendsto_source_segment_snd φ ψ ht₂)
  have hcΔ : Continuous (canonicalDiscriminant (by simp) (periodOnePotential ψ)) :=
    continuousOn_univ.mp (analyticOnNhd_canonicalDiscriminant (by simp) (by norm_num)
      (periodOnePotential ψ) (periodOnePotential_mem ψ)).continuousOn
  have hsquare : TendstoUniformlyOn
      (fun t : α × Icc (0 : ℝ) 1 => fun z => (canonicalDiscriminant (by simp) (periodOnePotential (a t)) z)^2)
      (fun z => (canonicalDiscriminant (by simp) (periodOnePotential ψ) z)^2) (l ×ˢ ⊤) K := by
    simpa only [pow_two,Pi.mul_apply] using!
      tendstoLocallyUniformly_iff_forall_isCompact.mp (hΔ.mul₀ hΔ hcΔ hcΔ) K hK
  have hcroot := (sourceCanonicalRoot_analyticOnNhd (by simp) (by norm_num) ψ).continuousOn.mono hKψ
  obtain ⟨δ,hδ,hδbound⟩ := hK.exists_forall_le' hcroot.norm (fun z hz =>
    norm_pos_iff.mpr (sourceCanonicalRoot_ne_zero_off_gaps (by simp) (by norm_num) ψ z (hKψ hz)))
  obtain ⟨W,_,_,hreal,_,hroot⟩ := exists_global_source_analytic_canonicalRoot (p := 2) (by simp) (by norm_num)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := Metric.tendstoUniformlyOn_iff.mp hsquare (δ*min δ ε) (by positivity)
  rw [← principal_univ,eventually_prod_principal_iff] at he
  filter_upwards [hseg,he] with k hk he z hz
  let q : ℝ → ℂ := fun t => sourceCanonicalRoot (by simp) (by norm_num) (BoundedSegmentLimits.segment ψ (φ k) t) z
  have hq : ContinuousOn q (Icc (0 : ℝ) 1) := by
    intro t ht'
    have hpoint : (z,BoundedSegmentLimits.segment ψ (φ k) t) ∈ sourceCanonicalRootJointDomain (by simp) (by norm_num) W :=
      ⟨hreal (isRealType_source_segment (φ k) ψ (hφ k) hψ t),hk t ht' hz⟩
    have hpath : Continuous (fun s : ℝ => (z,BoundedSegmentLimits.segment ψ (φ k) s)) :=
      continuous_const.prodMk (BoundedSegmentLimits.continuous_segment ψ (φ k))
    exact ((hroot _ hpoint).continuousAt.comp
      (f := fun s : ℝ => (z,BoundedSegmentLimits.segment ψ (φ k) s)) hpath.continuousAt).continuousWithinAt
  have hsq (t : ℝ) (ht' : t ∈ Icc (0 : ℝ) 1) :
      ‖q t^2-(sourceCanonicalRoot (by simp) (by norm_num) ψ z)^2‖ < δ*min δ ε := by
    have h := he ⟨t,ht'⟩ (mem_univ _) z hz
    rw [dist_eq_norm,norm_sub_rev] at h
    dsimp only [q]
    rw [sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four (by simp) (by norm_num) _ z (hk t ht' hz),
      sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four (by simp) (by norm_num) ψ z (hKψ hz)]
    simpa only [sub_sub_sub_cancel_right] using h
  have h := NLS.ComplexAnalysis.norm_sub_lt_of_square_path q _ δ ε hδ hε (hδbound z hz) hq
    (by simp [q]) hsq
  simpa only [q,BoundedSegmentLimits.segment_one,dist_eq_norm,norm_sub_rev] using h

end NLS.ZakharovShabat
