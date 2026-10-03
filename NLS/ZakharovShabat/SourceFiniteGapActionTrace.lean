import NLS.ZakharovShabat.SourceFiniteGapExteriorMass
import NLS.ZakharovShabat.SourceRealActionRealCenteredCircle

/-! # The finite-gap action–mass trace identity

Decompose a large weighted contour around the finitely many open gaps.
The filled logarithmic derivative is analytic through every closed gap.
-/
noncomputable section
open Set Complex Metric NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The sum over the actual open gaps equals the original Hilbert source mass. -/
theorem sourceFiniteGap_sum_actions_eq_mass
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    (∑ n ∈ hf.toFinset, sourceRealAction (by simp) (by norm_num) φ.val φ.property n) =
      sourceHilbertMass φ.val := by
  classical
  let hp : (2 : ENNReal) ≠ ⊤ := by simp
  let hp1 : (1 : ENNReal) < 2 := by norm_num
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
  obtain ⟨T, hT, hmass⟩ := exists_sourceFiniteGap_weighted_contour_eq_mass φ hf
  let S := max B T + 1
  have hTS : T ≤ S := by dsimp [S]; linarith [le_max_right B T]
  have hS : 0 < S := hT.trans_le hTS
  have henclosed (n : ℤ) (hn : n ∈ s) : closedBall (c n) (C.outer n) ⊆ ball 0 S := by
    intro z hz
    have hb := hB z (Set.mem_iUnion₂.mpr ⟨n, hn, hz⟩)
    rw [mem_ball, dist_zero_right]
    dsimp [S]
    linarith [le_max_left B T]
  have ha : AnalyticOnNhd ℂ (fun z => z * sourceFloquetLogDerivative hp hp1 φ.val z)
      (circleHoleDomain 0 S s c C.inner) := by
    intro z hz
    apply analyticAt_id.mul
    apply sourceFloquetLogDerivative_analyticOnNhd hp hp1 φ.val φ.property z
    intro n hn hzn
    exact hz.2 n ((hs n).mpr hn) (C.gap_enclosed n hzn)
  have hdec := circleIntegral_eq_sum_of_finite_holes 0 S hS.le s c C.inner C.outer
    (fun z => z * sourceFloquetLogDerivative hp hp1 φ.val z) (fun n _ => C.inner_pos n)
    (fun n _ => C.collar n) henclosed (fun n _ m _ hnm => C.disjoint_discs n m hnm) ha
  have hinner (n : ℤ) :
      (∮ z in C(c n,C.inner n), z * sourceFloquetLogDerivative hp hp1 φ.val z) =
        (Real.pi : ℂ) * sourceRealAction hp hp1 φ.val φ.property n := by
    obtain ⟨hr, hseg, hother, hcircle⟩ := C.contour_family.2 n
    rw [sourceRealAction_eq_realCentered_enclosingCircle hp hp1 φ.val φ.property n
      (c n) (C.inner n) (C.contour_family.1 n) hr hseg hother]
    rw [sourceActionCircle, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Real.pi_ne_zero), one_mul]
    apply circleIntegral.integral_congr hr.le
    intro z hz
    exact congrArg (fun w : ℂ => z * w)
      (sourceFloquetLogDerivative_eq_criticalRootRatio hp hp1 φ.val φ.property z (hcircle hz))
  have he := hmass S hTS
  rw [hdec] at he
  simp_rw [hinner] at he
  rw [← Finset.mul_sum] at he
  exact mul_left_cancel₀ (by exact_mod_cast Real.pi_ne_zero) he

end NLS.ZakharovShabat
