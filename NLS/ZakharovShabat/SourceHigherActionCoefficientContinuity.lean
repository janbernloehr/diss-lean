import NLS.ZakharovShabat.SourceActionCoefficientContinuity
import NLS.ZakharovShabat.SourceHigherActionRegularity

/-! # Higher Dirac actions under bounded coefficient limits

The fixed real-centered isolating circle persists along the actual real
source segments. Polynomial weights preserve uniform contour convergence.
Every indexed higher action therefore survives bounded coefficient limits,
including at collapsed gaps, without a spectral finite-gap hypothesis.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_source_higherActionCircle_along_segments_of_bounded_coefficientwise
    {α : Type*} {l : Filter α}
    (φ : α → CoeffPair 2) (ψ : CoeffPair 2) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ j, IsRealType (CoeffPair.toMax 2 (φ j))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun j => (φ j).fst n) l (𝓝 (ψ.fst n))) (n : ℤ) (k : ℕ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) ψ ∧
      sourceHigherActionCircle (by simp) (by norm_num) ψ c R k =
        (sourceRealHigherAction (by simp) (by norm_num) ⟨ψ,hψ⟩ n k : ℂ) ∧
      ∀ᶠ j in l, (∀ t ∈ Icc (0 : ℝ) 1, sphere c R ⊆
        sourceCanonicalRootDomain (by simp) (by norm_num) (BoundedSegmentLimits.segment ψ (φ j) t)) ∧
        sourceHigherActionCircle (by simp) (by norm_num) (φ j) c R k =
          (sourceRealHigherAction (by simp) (by norm_num) ⟨φ j,hφ j⟩ n k : ℂ) := by
  let a : α × Icc (0 : ℝ) 1 → CoeffPair 2 := fun t => BoundedSegmentLimits.segment ψ (φ t.1) t.2
  have hreal (t : α × Icc (0 : ℝ) 1) : IsRealType (CoeffPair.toMax 2 (a t)) :=
    isRealType_source_segment (φ t.1) ψ (hφ t.1) hψ t.2
  obtain ⟨c,R,hR,hc,hlim,he⟩ := exists_source_actionCircle_of_bounded_coefficientwise
    (by simp) (by norm_num) a ψ (BoundedSegmentLimits.bounded_range_segment φ ψ hb)
    hreal hψ (tendsto_source_segment_fst φ ψ ht) n
  refine ⟨c,R,hR,sourceCanonicalRootDomain_of_enclosingCircle (by simp) (by norm_num)
    ψ n c R hlim.1 hlim.2.1,
    sourceHigherActionCircle_eq_real_of_realCentered_enclosingCircle (by simp) (by norm_num)
      ⟨ψ,hψ⟩ n k c R hc hR hlim.1 hlim.2.1,?_⟩
  rw [←principal_univ,eventually_prod_principal_iff] at he
  filter_upwards [he] with j hj
  constructor
  · intro t ht'
    have h := hj ⟨t,ht'⟩ (mem_univ _)
    exact sourceCanonicalRootDomain_of_enclosingCircle (by simp) (by norm_num) _ n c R h.1 h.2.1
  · have h := hj ⟨1,by simp⟩ (mem_univ _)
    have hseg := h.1
    have hother := h.2.1
    simp only [a,BoundedSegmentLimits.segment_one] at hseg hother
    exact sourceHigherActionCircle_eq_real_of_realCentered_enclosingCircle (by simp) (by norm_num)
      ⟨φ j,hφ j⟩ n k c R hc hR hseg hother

theorem tendsto_sourceHigherActionCircle_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair 2) (ψ : CoeffPair 2) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ j, IsRealType (CoeffPair.toMax 2 (φ j))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun j => (φ j).fst n) l (𝓝 (ψ.fst n)))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (k : ℕ)
    (hc : sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) ψ)
    (hseg : ∀ᶠ j in l, ∀ t ∈ Icc (0 : ℝ) 1, sphere c R ⊆
      sourceCanonicalRootDomain (by simp) (by norm_num) (BoundedSegmentLimits.segment ψ (φ j) t)) :
    Tendsto (fun j => sourceHigherActionCircle (by simp) (by norm_num) (φ j) c R k) l
      (𝓝 (sourceHigherActionCircle (by simp) (by norm_num) ψ c R k)) := by
  have hq := tendstoUniformlyOn_sourceCriticalRootRatio_of_bounded_coefficientwise
    φ ψ hb hφ hψ ht (sphere c R) (isCompact_sphere c R) hc hseg
  have hp : TendstoUniformlyOn (fun _ : α => fun z : ℂ => z^(k+1)) (fun z => z^(k+1)) l (sphere c R) := by
    intro U hU
    exact Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU
  have hcq := (sourceCriticalRootRatio_analyticOnNhd (by simp) (by norm_num) ψ).continuousOn.mono hc
  have hw := hp.tendstoLocallyUniformlyOn.mul₀ hq.tendstoLocallyUniformlyOn (continuousOn_id.pow (k+1)) hcq
  have hu : TendstoUniformlyOn
      (fun j z => z^(k+1)*sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,φ j))
      (fun z => z^(k+1)*sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,ψ)) l (sphere c R) := by
    simpa only [Pi.mul_apply] using!
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere c R)).mp hw
  have hcont : ∀ᶠ j in l, ContinuousOn
      (fun z => z^(k+1)*sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,φ j)) (sphere c R) := by
    filter_upwards [hseg] with j hj
    have hd : sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (φ j) := by
      simpa only [BoundedSegmentLimits.segment_one] using hj 1 (by simp)
    exact (continuousOn_id.pow (k+1)).mul
      ((sourceCriticalRootRatio_analyticOnNhd (by simp) (by norm_num) (φ j)).continuousOn.mono hd)
  exact (hu.tendsto_circleIntegral_of_continuousOn hR hcont).const_mul _

/-- Every printed higher-action level, at every fixed signed index,
is continuous under bounded coefficientwise convergence of real L2 pairs. -/
theorem tendsto_sourceRealHigherAction_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair 2) (ψ : CoeffPair 2) (hb : Bornology.IsBounded (range φ))
    (hφ : ∀ j, IsRealType (CoeffPair.toMax 2 (φ j))) (hψ : IsRealType (CoeffPair.toMax 2 ψ))
    (ht : ∀ n : ℤ, Tendsto (fun j => (φ j).fst n) l (𝓝 (ψ.fst n))) (n : ℤ) (k : ℕ) :
    Tendsto (fun j => sourceRealHigherAction (by simp) (by norm_num) ⟨φ j,hφ j⟩ n k) l
      (𝓝 (sourceRealHigherAction (by simp) (by norm_num) ⟨ψ,hψ⟩ n k)) := by
  obtain ⟨c,R,hR,hc,hlim,he⟩ :=
    exists_source_higherActionCircle_along_segments_of_bounded_coefficientwise φ ψ hb hφ hψ ht n k
  have hcomplex : Tendsto
      (fun j => (sourceRealHigherAction (by simp) (by norm_num) ⟨φ j,hφ j⟩ n k : ℂ)) l
      (𝓝 (sourceRealHigherAction (by simp) (by norm_num) ⟨ψ,hψ⟩ n k : ℂ)) := by
    rw [←hlim]
    apply (tendsto_sourceHigherActionCircle_of_bounded_coefficientwise φ ψ hb hφ hψ ht c R hR.le k hc
      (he.mono fun _ hj => hj.1)).congr'
    exact he.mono fun _ hj => hj.2
  simpa only [Function.comp_def,ofReal_re] using
    Complex.continuous_re.continuousAt.tendsto.comp hcomplex

end NLS.ZakharovShabat
