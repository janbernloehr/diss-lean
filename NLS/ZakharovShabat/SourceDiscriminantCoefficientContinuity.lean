import NLS.ZakharovShabat.SourceDiscriminantCotangentDecay
import NLS.SequenceSpaces.UniformDualCoefficientLimits
import NLS.FunctionalAnalysis.BoundedSegmentLimits
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! # Discriminant convergence under bounded Hilbert coefficient limits

The actual discriminant cotangents have a common square-summable Fourier
majorant on bounded source and spectral balls. Their values on bounded
coefficient-null directions therefore tend uniformly to zero. Applying
this along the actual straight source segments proves uniform convergence
of the discriminant on bounded spectral sets, without strong convergence
or any real-type assumption.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.BoundedSegmentLimits
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The genuine cotangent applied to bounded coefficient-null directions
vanishes uniformly over bounded complex source and spectral balls. -/
theorem eventually_small_sourceDiscriminantCotangent_apply
    {α : Type*} {l : Filter α} (h : α → CoeffPair 2)
    (hb : Bornology.IsBounded (range h))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (h k).fst n) l (𝓝 0))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (h k).snd n) l (𝓝 0))
    (M R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in l, ∀ (φ : CoeffPair 2), ‖φ‖ ≤ M → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖sourceDiscriminantCotangent (by simp) z φ (h k)‖ < ε := by
  obtain ⟨B,hB⟩ := hb.exists_norm_le
  have hb₁ : Bornology.IsBounded (range (fun k => (h k).fst)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B,?_⟩
    rintro _ ⟨k,rfl⟩
    exact (WithLp.norm_fst_le _ (h k)).trans (hB _ ⟨k,rfl⟩)
  have hb₂ : Bornology.IsBounded (range (fun k => (h k).snd)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B,?_⟩
    rintro _ ⟨k,rfl⟩
    exact (WithLp.norm_snd_le _ (h k)).trans (hB _ ⟨k,rfl⟩)
  obtain ⟨b,hmajor⟩ := exists_sourceDiscriminantCotangent_coefficient_majorant M R hR
  filter_upwards [Coeff.eventually_small_dualPairing_of_bounded_coefficientwise
      (by simp) (fun k => (h k).fst) hb₁ ht₁ b (ε/2) (by positivity),
    Coeff.eventually_small_dualPairing_of_bounded_coefficientwise
      (by simp) (fun k => (h k).snd) hb₂ ht₂ b (ε/2) (by positivity)] with k hk₁ hk₂ φ hφ z hz
  let L := sourceDiscriminantCotangent (by simp) z φ
  let g := CoeffPair.cotangentCoefficients (by norm_num : (2 : ℝ≥0∞) ≤ 2) L
  have h₁ := hk₁ g.1 (fun n => (hmajor φ hφ z hz n).1)
  have h₂ := hk₂ g.2 (fun n => (hmajor φ hφ z hz n).2)
  have he : Coeff.dualPairing g.1 (h k).fst+Coeff.dualPairing g.2 (h k).snd = L (h k) := by
    have hi : CoeffPair.exponentInclusion (le_refl (2 : ℝ≥0∞)) (h k) = h k := by
      apply (CoeffPair.toMax 2).injective
      apply Prod.ext <;> ext n <;> rfl
    simpa only [hi] using CoeffPair.dualPairing_cotangentCoefficients (le_refl (2 : ℝ≥0∞)) L (h k)
  rw [← he]
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- Differentiating the actual discriminant along a real source segment
uses the original complex cotangent on the endpoint difference. -/
theorem hasDerivAt_sourceDiscriminant_segment (a b : CoeffPair 2) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => canonicalDiscriminant (by simp)
      (periodOnePotential (NLS.BoundedSegmentLimits.segment b a s)) z)
      (sourceDiscriminantCotangent (by simp) z (NLS.BoundedSegmentLimits.segment b a t) (a-b)) t := by
  have hseg : HasDerivAt (NLS.BoundedSegmentLimits.segment b a) (a-b) t := by
    convert! ((Complex.ofRealCLM.hasDerivAt (x := t)).smul_const (a-b)).const_add b using 1
    simp
  have hF := ((analyticOnNhd_canonicalDiscriminant_periodOne (p := 2) (by simp) (by norm_num)
    (z,NLS.BoundedSegmentLimits.segment b a t) (mem_univ _)).comp
    (f := fun χ : CoeffPair 2 => (z,χ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  exact (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hseg

/-- Bounded coefficient convergence gives one eventual discriminant estimate
for every spectral point in the chosen ball. -/
theorem eventually_norm_sourceDiscriminant_sub_lt_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (a : α → CoeffPair 2) (b : CoeffPair 2)
    (hb : Bornology.IsBounded (range a))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (a k).fst n) l (𝓝 (b.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (a k).snd n) l (𝓝 (b.snd n)))
    (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in l, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖canonicalDiscriminant (by simp) (periodOnePotential (a k)) z-
        canonicalDiscriminant (by simp) (periodOnePotential b) z‖ < ε := by
  obtain ⟨B,hB⟩ := hb.exists_norm_le
  have hdiff : Bornology.IsBounded (range (fun k => a k-b)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B+‖b‖,?_⟩
    rintro _ ⟨k,rfl⟩
    exact (norm_sub_le _ _).trans (by linarith [hB _ ⟨k,rfl⟩])
  have ht₁' (n : ℤ) : Tendsto (fun k => (a k-b).fst n) l (𝓝 0) := by
    simpa using (ht₁ n).sub_const (b.fst n)
  have ht₂' (n : ℤ) : Tendsto (fun k => (a k-b).snd n) l (𝓝 0) := by
    simpa using (ht₂ n).sub_const (b.snd n)
  obtain ⟨M,hM⟩ := (bounded_range_segment a b hb).exists_norm_le
  filter_upwards [eventually_small_sourceDiscriminantCotangent_apply (fun k => a k-b)
    hdiff ht₁' ht₂' M R hR (ε/2) (by positivity)] with k hk z hz
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖sourceDiscriminantCotangent (by simp) z (NLS.BoundedSegmentLimits.segment b (a k) t) (a k-b)‖ ≤ ε/2 :=
    (hk _ (hM _ ⟨(k,⟨t,ht⟩),rfl⟩) z hz).le
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_sourceDiscriminant_segment (a k) b z t).hasDerivWithinAt)
    hbound (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  simp only [segment_one,segment_zero,sub_zero,norm_one,mul_one] at h
  exact h.trans_lt (by linarith)

/-- The actual discriminants converge uniformly on every bounded spectral
set, for arbitrary filters and bounded complex Hilbert coefficient limits. -/
theorem tendstoUniformlyOn_sourceDiscriminant_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (a : α → CoeffPair 2) (b : CoeffPair 2)
    (hb : Bornology.IsBounded (range a))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (a k).fst n) l (𝓝 (b.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (a k).snd n) l (𝓝 (b.snd n)))
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun k => canonicalDiscriminant (by simp) (periodOnePotential (a k)))
      (canonicalDiscriminant (by simp) (periodOnePotential b)) l K := by
  obtain ⟨R,hR⟩ := hK.exists_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_norm_sourceDiscriminant_sub_lt_of_bounded_coefficientwise
    a b hb ht₁ ht₂ (max R 0) (le_max_right _ _) ε hε] with k hk z hz
  simpa only [dist_eq_norm,norm_sub_rev] using hk z ((hR z hz).trans (le_max_left _ _))

/-- Locally uniform convergence of the entire actual discriminant family. -/
theorem tendstoLocallyUniformly_sourceDiscriminant_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (a : α → CoeffPair 2) (b : CoeffPair 2)
    (hb : Bornology.IsBounded (range a))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (a k).fst n) l (𝓝 (b.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (a k).snd n) l (𝓝 (b.snd n))) :
    TendstoLocallyUniformly (fun k => canonicalDiscriminant (by simp) (periodOnePotential (a k)))
      (canonicalDiscriminant (by simp) (periodOnePotential b)) l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  exact fun K hK => tendstoUniformlyOn_sourceDiscriminant_of_bounded_coefficientwise a b hb ht₁ ht₂ K hK.isBounded

/-- In particular, every fixed discriminant value converges without a
strong source-norm limit or real-type hypothesis. -/
theorem tendsto_sourceDiscriminant_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (a : α → CoeffPair 2) (b : CoeffPair 2)
    (hb : Bornology.IsBounded (range a))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (a k).fst n) l (𝓝 (b.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (a k).snd n) l (𝓝 (b.snd n))) (z : ℂ) :
    Tendsto (fun k => canonicalDiscriminant (by simp) (periodOnePotential (a k)) z) l
      (𝓝 (canonicalDiscriminant (by simp) (periodOnePotential b) z)) :=
  (tendstoLocallyUniformly_sourceDiscriminant_of_bounded_coefficientwise a b hb ht₁ ht₂).tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)

end NLS.ZakharovShabat
