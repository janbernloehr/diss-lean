import NLS.ZakharovShabat.SourceFiniteGapExterior
import NLS.ZakharovShabat.SourcePsiIsolatingCircles
import NLS.ZakharovShabat.SourceNormalizedActionUniformCircleRealAgreement
import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition

/-! # Vanishing exterior period of the finite-gap logarithmic derivative

Only open gaps are removed from the finite-hole domain. The regularized
quotient is analytic at all remaining collapsed points. Its inner periods
are the already proved zero gap periods, so every sufficiently large
outer circle has zero period as well.
-/
noncomputable section
open Set Complex Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The regularized logarithmic derivative has zero integral on every
sufficiently large centered circle, at each actual real finite-gap source. -/
theorem exists_sourceFiniteGap_exterior_period_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ S : ℝ, T ≤ S →
      (∮ z in C(0,S), sourceFloquetLogDerivative hp hp1 φ.val z) = 0 := by
  classical
  obtain ⟨N, ε, _, _, U, _, _, hφU, hcluster, hdisj⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ.val φ.property
  have hgap (n : ℤ) := sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val φ.val N ε n
    (hcluster φ.val hφU n)
  obtain ⟨C⟩ := nonempty_sourcePsiIsolatingCircleFamily hp hp1 φ.val φ.val N ε hgap hdisj
  let c := sourceIsolatingCenter hp hp1 φ.val N
  let s : Finset ℤ := hf.toFinset
  have hs (n : ℤ) : n ∈ s ↔ canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0 := Set.Finite.mem_toFinset hf
  have hc : IsCompact (⋃ n ∈ s, closedBall (c n) (C.outer n)) :=
    s.finite_toSet.isCompact_biUnion fun n _ => isCompact_closedBall _ _
  obtain ⟨B, hB⟩ := hc.isBounded.exists_norm_le
  let T := max B 0 + 1
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T, hT, ?_⟩
  intro S hS
  have hSpos : 0 < S := hT.trans_le hS
  have henclosed (n : ℤ) (hn : n ∈ s) : closedBall (c n) (C.outer n) ⊆ ball 0 S := by
    intro z hz
    have hb := hB z (Set.mem_iUnion₂.mpr ⟨n, hn, hz⟩)
    rw [mem_ball, dist_zero_right]
    have hBT : B < T := by dsimp [T]; linarith [le_max_left B 0]
    exact (hb.trans_lt hBT).trans_le hS
  have ha : AnalyticOnNhd ℂ (sourceFloquetLogDerivative hp hp1 φ.val)
      (circleHoleDomain 0 S s c C.inner) := by
    apply (sourceFloquetLogDerivative_analyticOnNhd hp hp1 φ.val φ.property).mono
    intro z hz n hn hzn
    exact hz.2 n ((hs n).mpr hn) (C.gap_enclosed n hzn)
  have hdec := circleIntegral_eq_sum_of_finite_holes 0 S hSpos.le s c C.inner C.outer
    (sourceFloquetLogDerivative hp hp1 φ.val) (fun n _ => C.inner_pos n)
    (fun n _ => C.collar n) henclosed (fun n _ m _ hnm => C.disjoint_discs n m hnm) ha
  rw [hdec]
  apply Finset.sum_eq_zero
  intro n _
  obtain ⟨hr, hseg, hother, hcircle⟩ := C.contour_family.2 n
  calc
    (∮ z in C(c n,C.inner n), sourceFloquetLogDerivative hp hp1 φ.val z) =
        ∮ z in C(c n,C.inner n), sourceCriticalRootRatioJoint hp hp1 (z,φ.val) := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      exact sourceFloquetLogDerivative_eq_criticalRootRatio hp hp1 φ.val φ.property z (hcircle hz)
    _ = 0 := sourceCriticalRootRatio_enclosingCircleIntegral_zero_of_realType_allGaps
      hp hp1 φ.val φ.property n (c n) (C.inner n) hr hseg hother

end NLS.ZakharovShabat
