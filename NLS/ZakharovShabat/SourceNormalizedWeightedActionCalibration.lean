import NLS.ZakharovShabat.SourceNormalizedWeightedAction
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedPositive

/-! # Calibration of the filled normalized moment at a closed gap

The actual Cauchy equation fixes the midpoint value of its primitive
quotient. Thus the unweighted normalized moment is the SAME canonical
normalized action at every real source, including collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem quotient_collapsed_midpoint
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0)
    (hcrit : canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      sourceStandardRootMidpoint hp hp1 ψ n) :
    sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n)
        (sourceStandardRootMidpoint hp hp1 ψ n,ψ) =
      -sourceCriticalRootRatioExtension hp hp1 n ψ (sourceStandardRootMidpoint hp hp1 ψ n) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let Q : ℂ → ℂ := fun z => sourceFullAbelianCauchyQuotient hp hp1 W n
    (C.discs.center n) (C.discs.outer n) (z,ψ)
  let E := sourceCriticalRootRatioExtension hp hp1 n ψ
  have hτ : τ ∈ ball (C.discs.center n) (C.discs.outer n) :=
    C.segment_subset_outer n ψ hψ (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hQa : AnalyticAt ℂ Q τ := C.quotient_slice_analytic n ψ hψ τ hτ
  have hEa : AnalyticAt ℂ E τ := C.extension_analytic ψ hψ n τ
    (C.discs.avoids_other ψ hψ n (ball_subset_closedBall hτ))
  obtain ⟨D⟩ := C.charts ψ hψ
  have heq : ∀ z ∈ ball (C.discs.center n) (C.discs.outer n),
      (z-τ)^2*deriv Q z+(z-τ)*Q z = (τ-z)*E z := by
    intro z hz
    have he := sourceFullAbelianCauchyQuotient_equation hp hp1 W ψ n
      (C.discs.center n) (C.discs.outer n) ((C.discs.inner_pos n).trans (C.discs.inner_lt n)) D
      (C.circle_root n ψ hψ) (C.discs.avoids_other ψ hψ n) (C.extension_analytic ψ hψ n) z hz
    simpa only [sourceAngularSelectedPolynomial,quadraticRootPolynomial,hgap,
      zero_pow (by norm_num : 2 ≠ 0),zero_div,sub_zero,sourceCriticalRootGapNumerator,hcrit] using he
  have he : ∀ᶠ z in 𝓝[≠] τ, (z-τ)*deriv Q z+Q z = -E z := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hτ),self_mem_nhdsWithin]
      with z hz hne
    apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
    calc
      (z-τ)*((z-τ)*deriv Q z+Q z) = (z-τ)^2*deriv Q z+(z-τ)*Q z := by ring
      _ = (τ-z)*E z := heq z hz
      _ = (z-τ)*(-E z) := by ring
  have hleft : ContinuousAt (fun z : ℂ => (z-τ)*deriv Q z+Q z) τ :=
    ((continuousAt_id.sub continuousAt_const).mul hQa.deriv.continuousAt).add hQa.continuousAt
  have hv := tendsto_nhds_unique_of_eventuallyEq
    (hleft.tendsto.mono_left nhdsWithin_le_nhds)
    (hEa.continuousAt.neg.tendsto.mono_left nhdsWithin_le_nhds) he
  change Q τ = -E τ
  simpa only [sub_self,zero_mul,zero_add,Pi.neg_apply] using hv

theorem normalizedWeightedAction_zero_collapsed
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0)
    (hcrit : canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      sourceStandardRootMidpoint hp hp1 ψ n) :
    C.normalizedWeightedAction n 0 ψ = sourceNormalizedActionCollapsedCandidate hp hp1 n ψ := by
  have hQ := C.quotient_collapsed_midpoint ψ hψ n hgap hcrit
  have hs : (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2) = (Real.pi : ℂ)/2 := by
    simp_rw [← ofReal_pow]
    rw [intervalIntegral.integral_ofReal]
    simp only [integral_sin_sq,Real.sin_zero,Real.sin_pi,zero_mul,
      sub_zero,sub_self,zero_add,ofReal_div,ofReal_ofNat]
  simp only [normalizedWeightedAction,parametricSineSquareCosineMean,sourceStandardRootHalfGap,
    hgap,zero_div,zero_mul,add_zero,pow_zero,one_mul]
  rw [intervalIntegral.integral_mul_const,hs,hQ]
  unfold sourceNormalizedActionCollapsedCandidate
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

theorem normalizedWeightedAction_zero_eq_canonical
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) :
    C.normalizedWeightedAction n 0 φ.val = sourceNormalizedActionComplexExtension hp hp1 n φ.val := by
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · obtain ⟨_,_,_,hreal,hexact⟩ := exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
    have hg : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0 := by
      simpa only [sourcePeriodicGapDisplacement_apply] using hgap
    have hcrit : canonicalCriticalPoints hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n =
        sourceStandardRootMidpoint hp hp1 φ.val n := by
      have he := (hexact φ.val (hreal φ.property) n).2
      rw [hg,zero_pow (by norm_num : 2 ≠ 0),zero_mul] at he
      exact sub_eq_zero.mp he
    rw [C.normalizedWeightedAction_zero_collapsed φ.val hφ n hgap hcrit]
    simp only [sourceNormalizedActionComplexExtension,sourceNormalizedActionRealExtension,hg,ite_true]
  · let A := sourceHigherActionAtlas hp hp1
    obtain ⟨r,hr,_,hfactor⟩ := C.exists_ball_normalizedWeightedActions A φ hφ
    have hF := (hfactor n 0).2 φ.val (mem_ball_self hr)
    have hA : A.action n 0 φ.val = sourceComplexAction hp hp1 n φ.val :=
      A.action_zero n ⟨A.realType_subset_domain φ.property,
        realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 n φ.property⟩
    obtain ⟨U,_,hφU,_,hcanonical⟩ :=
      exists_local_sourceNormalizedActionComplexExtension_differentiableOn hp hp1 φ.val φ.property n
    apply mul_left_cancel₀ (pow_ne_zero 2 hgap)
    exact hF.symm.trans (hA.trans (by
      simpa only [sourcePeriodicGapDisplacement_apply] using hcanonical φ.val hφU))

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
