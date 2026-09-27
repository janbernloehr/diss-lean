import NLS.ZakharovShabat.SourceNormalizedActionComplexDerivative
import NLS.ZakharovShabat.RealCriticalSimplicity
import NLS.ZakharovShabat.SourceNormalizedActionPositive

/-!
# Nonvanishing of the normalized action at collapsed real gaps

The deleted critical product cannot vanish at a simple critical root:
otherwise restoring the selected linear factor would give a double
zero of the discriminant derivative. This makes the deleted quotient,
and hence the normalized-action extension, nonzero at a collapsed
real gap.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Deleting a simple root from the entire critical product leaves a
nonzero value at that root. -/
theorem jointDeletedSingleSpectralProduct_ne_zero_at_simple_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (z : ℂ)
    (hroot : displacedRoots a n = z)
    (hsimple : deriv (fun w : ℂ => jointSingleSpectralProduct (w,a)) z ≠ 0) :
    jointDeletedSingleSpectralProduct n (z,a) ≠ 0 := by
  let D : ℂ → ℂ := fun w => jointDeletedSingleSpectralProduct n (w,a)
  have hD : DifferentiableAt ℂ D z := by
    have hjoint := (analyticOnNhd_jointDeletedSingleSpectralProduct hp hp1 n)
      (z,a) (mem_univ _)
    have hmap : AnalyticAt ℂ (fun w : ℂ => (w,a)) z :=
      analyticAt_id.prod analyticAt_const
    exact (hjoint.comp (f := fun w : ℂ => (w,a)) hmap).differentiableAt
  have hlinear : HasDerivAt (fun w : ℂ => displacedRoots a n - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (displacedRoots a n)
  have hfactor : (fun w : ℂ => jointSingleSpectralProduct (w,a)) =
      fun w => 2*(displacedRoots a n-w)*D w := by
    funext w
    exact jointSingleSpectralProduct_eq_deleted hp hp1 n (w,a)
  intro hzero
  have hprod := (hlinear.mul hD.hasDerivAt).const_mul (2:ℂ)
  apply hsimple
  rw [hfactor]
  have hfun : (fun w : ℂ => 2*(displacedRoots a n-w)*D w) =
      fun w => 2*((fun w => displacedRoots a n-w)*D) w := by
    funext w
    simp only [Pi.mul_apply]
    ring
  rw [hfun]
  rw [hprod.deriv]
  simp [D,hroot,hzero]

/-- At a real-type source, the deleted critical numerator is nonzero
at its selected critical point. -/
theorem sourceDeletedCriticalProduct_ne_zero_at_realCriticalPoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    jointDeletedSingleSpectralProduct n
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n,
       canonicalCriticalDisplacement hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ)) ≠ 0 := by
  let φ := periodOnePotential ψ
  let a := canonicalCriticalDisplacement hp hp1 φ (periodOnePotential_mem ψ)
  let c := canonicalCriticalPoints hp hp1 φ (periodOnePotential_mem ψ) n
  have hroot : displacedRoots a n = c := by
    simp only [a,c,displacedRoots,canonicalCriticalDisplacement_apply]
    ring
  have hseq : displacedRoots a =
      canonicalCriticalPoints hp hp1 φ (periodOnePotential_mem ψ) := by
    funext m
    simp only [a,displacedRoots,canonicalCriticalDisplacement_apply]
    ring
  have hfun : (fun w : ℂ => jointSingleSpectralProduct (w,a)) =
      deriv (canonicalDiscriminant hp φ) := by
    funext w
    rw [discriminant_derivative_eq_canonicalCriticalProduct hp hp1
      φ (periodOnePotential_mem ψ) w]
    change entireSingleSpectralProduct (displacedRoots a) w = _
    rw [hseq]
  have hcrit : deriv (canonicalDiscriminant hp φ) c = 0 :=
    canonicalCriticalPoints_is_critical hp hp1 φ (periodOnePotential_mem ψ) n
  have hsimple : deriv (fun w : ℂ => jointSingleSpectralProduct (w,a)) c ≠ 0 := by
    rw [hfun]
    exact discriminant_second_derivative_ne_zero_at_critical_of_realType
      hp hp1 φ (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) c hcrit
  exact jointDeletedSingleSpectralProduct_ne_zero_at_simple_root
    hp hp1 n a c hroot hsimple

/-- The regular deleted quotient is nonzero at the midpoint of a
collapsed real-type gap. -/
theorem sourceCriticalRootRatioExtension_ne_zero_at_collapsedGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) :
    sourceCriticalRootRatioExtension hp hp1 n ψ
      (sourceStandardRootMidpoint hp hp1 ψ n) ≠ 0 := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let c := canonicalCriticalPoints hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hτc : τ = c := by
    have hcritical :=
      (exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1)
    obtain ⟨W,_,_,hWreal,hdata⟩ := hcritical
    have h := (hdata ψ (hWreal hreal) n).2
    rw [hgap] at h
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul] at h
    change c-τ = 0 at h
    exact (sub_eq_zero.mp h).symm
  have hnum : jointDeletedSingleSpectralProduct n
      (τ,canonicalCriticalDisplacement hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ)) ≠ 0 := by
    rw [hτc]
    exact sourceDeletedCriticalProduct_ne_zero_at_realCriticalPoint
      hp hp1 n ψ hreal
  have hdomain : τ ∈ sourceStandardRootOmittedDomain hp hp1 ψ n := by
    obtain ⟨W,_,_,hWreal,hdisjoint⟩ :=
      exists_global_source_disjoint_periodicSegments hp hp1
    intro m hmn hmem
    exact Set.disjoint_left.mp (hdisjoint ψ (hWreal hreal) n m (Ne.symm hmn))
      (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n) hmem
  have hden : sourceStandardRootOmittedProduct hp hp1 n ψ τ ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ τ n hdomain
  change -I *
    (jointDeletedSingleSpectralProduct n
      (τ,canonicalCriticalDisplacement hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ)) /
      sourceStandardRootOmittedProduct hp hp1 n ψ τ) ≠ 0
  exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (div_ne_zero hnum hden)

/-- The chart-independent normalized action does not vanish when a
real-type periodic gap collapses. -/
theorem sourceNormalizedActionComplexExtension_ne_zero_of_realType_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) :
    sourceNormalizedActionComplexExtension hp hp1 n ψ ≠ 0 := by
  have hE := sourceCriticalRootRatioExtension_ne_zero_at_collapsedGap
    hp hp1 n ψ hreal hgap
  simp only [sourceNormalizedActionComplexExtension,
    sourceNormalizedActionRealExtension, if_pos hgap,
    sourceNormalizedActionCollapsedCandidate]
  exact div_ne_zero (mul_ne_zero I_ne_zero hE) (by norm_num)

/-- The normalized-action extension is nonzero at every real-type
source, whether the selected gap is open or collapsed. -/
theorem sourceNormalizedActionComplexExtension_ne_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    sourceNormalizedActionComplexExtension hp hp1 n ψ ≠ 0 := by
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · exact sourceNormalizedActionComplexExtension_ne_zero_of_realType_zeroGap
      hp hp1 n ψ hreal hgap
  · have hpos := sourceRawNormalizedAction_re_pos_of_realType_gap_ne_zero
      hp hp1 n ψ hreal hgap
    have hraw : sourceRawNormalizedAction hp hp1 n ψ ≠ 0 := by
      intro he
      rw [he] at hpos
      norm_num at hpos
    simpa only [sourceNormalizedActionComplexExtension,
      sourceNormalizedActionRealExtension, if_neg hgap] using hraw

/-- For each fixed index, one open complex neighborhood of the full
real-type locus supports a nonvanishing differentiable normalized
action and its exact squared-gap factorization. -/
theorem exists_global_sourceNormalizedActionComplexExtension_nonzero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      DifferentiableOn ℂ (sourceNormalizedActionComplexExtension hp hp1 n) W ∧
      (∀ ψ ∈ W,
        sourceNormalizedActionComplexExtension hp hp1 n ψ ≠ 0) ∧
      ∀ ψ ∈ W,
        sourceComplexAction hp hp1 n ψ =
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
            sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  let F := sourceNormalizedActionComplexExtension hp hp1 n
  let P : Set (CoeffPair p) := {ψ | ∃ U : Set (CoeffPair p),
    IsOpen U ∧ ψ ∈ U ∧ ∀ χ ∈ U, F χ ≠ 0}
  have hPopen : IsOpen P := by
    apply isOpen_iff_mem_nhds.mpr
    intro ψ hψ
    obtain ⟨U,hUopen,hψU,hU⟩ := hψ
    exact Filter.mem_of_superset (hUopen.mem_nhds hψU)
      (fun χ hχ => ⟨U,hUopen,hχ,hU⟩)
  have hrealP : realTypeSourceLocus p ⊆ P := by
    intro ψ hreal
    have hne : F ψ ≠ 0 :=
      sourceNormalizedActionComplexExtension_ne_zero_of_realType
        hp hp1 n ψ hreal
    have hcont : ContinuousAt F ψ :=
      (differentiableAt_sourceNormalizedActionComplexExtension_of_realType
        hp hp1 ψ hreal n).continuousAt
    have hnear : ∀ᶠ χ : CoeffPair p in 𝓝 ψ, F χ ≠ 0 :=
      hcont.eventually (isOpen_ne.mem_nhds hne)
    obtain ⟨U,hUsub,hUopen,hψU⟩ := _root_.mem_nhds_iff.mp hnear
    exact ⟨U,hUopen,hψU,fun χ hχ => hUsub hχ⟩
  obtain ⟨D,hDopen,hrealD,_,hdiff,hfactor⟩ :=
    exists_global_sourceNormalizedActionComplexExtension_differentiableOn
      hp hp1 n
  let W := P ∩ D
  refine ⟨W,hPopen.inter hDopen,?_,hdiff.mono inter_subset_right,?_,?_⟩
  · intro ψ hreal
    exact ⟨hrealP hreal,hrealD hreal⟩
  · intro ψ hψ
    obtain ⟨U,_,hψU,hU⟩ := hψ.1
    exact hU ψ hψU
  · intro ψ hψ
    exact hfactor ψ hψ.2

end NLS.ZakharovShabat
