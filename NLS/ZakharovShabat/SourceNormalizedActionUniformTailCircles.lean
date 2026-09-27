import NLS.ZakharovShabat.SourceNormalizedActionCircleCorrectionBound
import NLS.ZakharovShabat.SourceCriticalGapQuotientContinuity

/-!
# Common distant-index circles for the normalized action

Locally uniform `ℓp` tails put the periodic midpoint and gap close
to their free values on one complex source neighborhood. A fixed
eighth-π circle around each distant free lattice point then encloses
the moving periodic segment and lies inside its quarter-π isolating
disc. These are the circles needed to apply the complex contour
correction estimate uniformly in the spectral index.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A coefficient outside a symmetric truncation is bounded by the
norm of that sequence's tail. -/
private theorem norm_coeff_apply_le_tail
    {p : ℝ≥0∞}
    (hp1 : 1 < p) (a : Coeff p) (N : ℕ) (n : ℤ)
    (hn : N < n.natAbs) :
    ‖a n‖ ≤ ‖a - Coeff.truncate (Finset.Icc (-(N : ℤ)) N) a‖ := by
  have hnot : n ∉ Finset.Icc (-(N : ℤ)) N := by
    simp only [Finset.mem_Icc]
    omega
  have hpoint := lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
    (a - Coeff.truncate (Finset.Icc (-(N : ℤ)) N) a) n
  simpa only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply,
    if_neg hnot, sub_zero] using hpoint

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Midpoint and gap displacements are simultaneously small at all
sufficiently distant signed indices on one complex neighborhood. -/
theorem exists_local_sourcePeriodicMidpointGap_tiny_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs →
        ‖sourceStandardRootMidpoint hp hp1 ψ n - (Real.pi:ℂ)*n‖ ≤
          Real.pi/64 ∧
        ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ ≤ Real.pi/32 := by
  obtain ⟨Nm,_,Vm,hVmopen,hφVm,_,_,hm⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ
      (by positivity : 0 < Real.pi/64)
  obtain ⟨Ng,_,Vg,hVgopen,hφVg,_,_,hg⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ
      (by positivity : 0 < Real.pi/32)
  let K := max Nm Ng + 1
  refine ⟨K,Vm ∩ Vg,hVmopen.inter hVgopen,⟨hφVm,hφVg⟩,?_⟩
  intro ψ hψ n hn
  have hNm : Nm < n.natAbs := by dsimp [K] at hn; omega
  have hNg : Ng < n.natAbs := by dsimp [K] at hn; omega
  have hmtail := (hm ψ hψ.1).2 Nm le_rfl
  have hgtail := (hg ψ hψ.2).2 Ng le_rfl
  constructor
  · simpa only [sourcePeriodicMidpointDisplacement_apply,
      sourceStandardRootMidpoint] using
      (norm_coeff_apply_le_tail hp1
        (sourcePeriodicMidpointDisplacement hp hp1 ψ) Nm n hNm).trans hmtail
  · simpa only [sourcePeriodicGapDisplacement_apply] using
      (norm_coeff_apply_le_tail hp1
        (sourcePeriodicGapDisplacement hp hp1 ψ) Ng n hNg).trans hgtail

/-- Small midpoint and gap displacements put the entire complex
periodic segment inside the free eighth-π circle. -/
theorem sourcePeriodicSegment_subset_free_eighth_ball
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ n - (Real.pi:ℂ)*n‖ ≤
      Real.pi/64)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ ≤ Real.pi/32) :
    sourcePeriodicSegment hp hp1 ψ n ⊆
      ball ((Real.pi:ℂ)*n) (Real.pi/8) := by
  let c : ℂ := (Real.pi:ℂ)*n
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ n
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have hl : l = τ-γ/2 := by
    simp only [l,τ,γ,
      sourcePeriodicGapDisplacement_apply,canonicalPeriodicMidpoint,
      canonicalPeriodicGap]
    ring
  have hr : r = τ+γ/2 := by
    simp only [r,τ,γ,
      sourcePeriodicGapDisplacement_apply,canonicalPeriodicMidpoint,
      canonicalPeriodicGap]
    ring
  have hhalf : ‖γ/2‖ ≤ Real.pi/64 := by
    rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    dsimp [γ] at hgap
    nlinarith
  have hleft : l ∈ ball c (Real.pi/8) := by
    rw [mem_ball, dist_eq_norm, hl]
    have heq : τ-γ/2-c = (τ-c)-γ/2 := by ring
    rw [heq]
    have hnorm := norm_sub_le (τ-c) (γ/2)
    nlinarith [Real.pi_pos]
  have hright : r ∈ ball c (Real.pi/8) := by
    rw [mem_ball, dist_eq_norm, hr]
    have heq : τ+γ/2-c = (τ-c)+γ/2 := by ring
    rw [heq]
    have hnorm := norm_add_le (τ-c) (γ/2)
    nlinarith [Real.pi_pos]
  change segment ℝ l r ⊆ ball c (Real.pi/8)
  exact (convex_ball c (Real.pi/8)).segment_subset hleft hright

/-- One complex source neighborhood and one cutoff give a common
family of free-centered circles. Each distant circle encloses its
moving complex gap, stays inside the existing isolating disc, and
meets the small-gap and separation assumptions of the correction
estimate. -/
theorem exists_local_sourceNormalizedAction_uniform_tail_circles
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs →
        sourcePeriodicSegment hp hp1 ψ n ⊆
          ball ((Real.pi:ℂ)*n) (Real.pi/8) ∧
        closedBall ((Real.pi:ℂ)*n) (Real.pi/8) ⊆
          refinedResonantDisk n ∧
        (∀ z ∈ sphere ((Real.pi:ℂ)*n) (Real.pi/8),
          Real.pi/16 ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖) ∧
        ‖(sourcePeriodicGapDisplacement hp hp1 ψ n)^2‖ ≤
          (Real.pi/16)^2 := by
  obtain ⟨K,V,hVopen,hφV,hdata⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail hp hp1 φ
  refine ⟨K,V,hVopen,hφV,?_⟩
  intro ψ hψ n hn
  obtain ⟨hmid,hgap⟩ := hdata ψ hψ n hn
  let c : ℂ := (Real.pi:ℂ)*n
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  have hseg := sourcePeriodicSegment_subset_free_eighth_ball
    hp hp1 ψ n hmid hgap
  have hsmall : Real.pi/8 < Real.pi/4 := by nlinarith [Real.pi_pos]
  have hdisc : closedBall c (Real.pi/8) ⊆ refinedResonantDisk n := by
    simpa only [refinedResonantDisk, c] using
      (Metric.closedBall_subset_ball hsmall :
        closedBall c (Real.pi/8) ⊆ ball c (Real.pi/4))
  refine ⟨hseg,hdisc,?_,?_⟩
  · intro z hz
    have hzNorm : ‖c-z‖ = Real.pi/8 := by
      simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hz
    have htri : ‖c-z‖ ≤ ‖τ-c‖+‖τ-z‖ := by
      have heq : c-z = (c-τ)+(τ-z) := by ring
      rw [heq]
      have h := norm_add_le (c-τ) (τ-z)
      rwa [norm_sub_rev] at h
    change Real.pi/16 ≤ ‖τ-z‖
    nlinarith [Real.pi_pos]
  · rw [norm_pow]
    have hsq := pow_le_pow_left₀
      (norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ n)) hgap 2
    nlinarith [sq_nonneg Real.pi]

/-- On one complex source neighborhood, every distant free-centered
circle encloses its selected gap, its filled disc avoids all other
periodic segments, and the deleted factor is analytic throughout
that filled disc. The quantitative separation needed for the
correction estimate holds on each circle. -/
theorem exists_local_sourceNormalizedAction_uniform_tail_circle_data
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs →
        sourcePeriodicSegment hp hp1 ψ n ⊆
          ball ((Real.pi:ℂ)*n) (Real.pi/8) ∧
        closedBall ((Real.pi:ℂ)*n) (Real.pi/8) ⊆
          sourceStandardRootOmittedDomain hp hp1 ψ n ∧
        AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 n ψ)
          (closedBall ((Real.pi:ℂ)*n) (Real.pi/8)) ∧
        (∀ z ∈ sphere ((Real.pi:ℂ)*n) (Real.pi/8),
          Real.pi/16 ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖) ∧
        ‖(sourcePeriodicGapDisplacement hp hp1 ψ n)^2‖ ≤
          (Real.pi/16)^2 := by
  obtain ⟨K₀,V₀,hV₀open,hφV₀,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circles hp hp1 φ
  obtain ⟨N,ε,_,_,V₁,hV₁open,_,hφV₁,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hφ
  obtain ⟨W,hWopen,hrealW,hEdata⟩ :=
    exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  let K := max K₀ (N+1)
  let V := (V₀ ∩ V₁) ∩ W
  refine ⟨K,V,(hV₀open.inter hV₁open).inter hWopen,
    ⟨⟨hφV₀,hφV₁⟩,hrealW hφ⟩,?_⟩
  intro ψ hψ n hn
  have hn₀ : K₀ ≤ n.natAbs := by dsimp [K] at hn; omega
  have hnN : N < n.natAbs := by dsimp [K] at hn; omega
  obtain ⟨hseg,hdisc,hsep,hq⟩ := hgeom ψ hψ.1.1 n hn₀
  have hsmall : Real.pi/8 < Real.pi/4 := by nlinarith [Real.pi_pos]
  have hdom : closedBall ((Real.pi:ℂ)*n) (Real.pi/8) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n := by
    have hiso := sourceIsolatingDisc_subset_omittedDomain
      hp hp1 φ ψ N ε (hcluster ψ hψ.1.2) hdisjoint n
    intro z hz
    apply hiso
    have hzdisc : z ∈ refinedResonantDisk n := hdisc hz
    simpa only [sourceIsolatingDisc, if_neg (not_le.mpr hnN)] using hzdisc
  have hE : AnalyticOnNhd ℂ
      (sourceCriticalRootRatioExtension hp hp1 n ψ)
      (closedBall ((Real.pi:ℂ)*n) (Real.pi/8)) := by
    intro z hz
    exact hEdata ψ hψ.2 n z (hdom hz)
  exact ⟨hseg,hdom,hE,hsep,hq⟩

end NLS.ZakharovShabat
