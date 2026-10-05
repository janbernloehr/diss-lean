import NLS.ZakharovShabat.SourceGapContourComparison
import NLS.ZakharovShabat.SourceFiniteGap
import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition

/-! # Contour decomposition outside finitely many open gaps

One radius threshold works for every function analytic off the open gaps.
The small contours may be any real-centered isolating family, and closed
gaps require no holes.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A large contour equals the sum over precisely the open gaps. -/
theorem exists_sourceFiniteGap_contour_decomposition
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (a : ℤ → ℂ) (r : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ.val a r) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R → ∀ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f (sourceOpenGapComplement hp hp1 φ.val) →
      (∮ z in C(0,R), f z) = ∑ k ∈ hf.toFinset, ∮ z in C(a k,r k), f z := by
  classical
  obtain ⟨N, ε, _, _, U, _, _, hφU, hcluster, hdisj⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ.val φ.property
  have hgap (k : ℤ) := sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val φ.val N ε k
    (hcluster φ.val hφU k)
  obtain ⟨C⟩ := nonempty_sourcePsiIsolatingCircleFamily hp hp1 φ.val φ.val N ε hgap hdisj
  let c := sourceIsolatingCenter hp hp1 φ.val N
  let S : Finset ℤ := hf.toFinset
  have hS (k : ℤ) : k ∈ S ↔ canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0 := Set.Finite.mem_toFinset hf
  have hc : IsCompact (⋃ k ∈ S, closedBall (c k) (C.outer k)) :=
    S.finite_toSet.isCompact_biUnion fun k _ => isCompact_closedBall _ _
  obtain ⟨B, hB⟩ := hc.isBounded.exists_norm_le
  let T := max B 0 + 1
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right B 0]
  refine ⟨T,hT,?_⟩
  intro R hTR f ha
  have hR : 0 ≤ R := (hT.trans_le hTR).le
  have henclosed (k : ℤ) (hk : k ∈ S) : closedBall (c k) (C.outer k) ⊆ ball 0 R := by
    intro z hz
    have hb := hB z (Set.mem_iUnion₂.mpr ⟨k,hk,hz⟩)
    rw [mem_ball,dist_zero_right]
    dsimp [T] at hTR
    linarith [le_max_left B 0]
  have hhole : AnalyticOnNhd ℂ f (circleHoleDomain 0 R S c C.inner) := by
    intro z hz
    apply ha z
    intro k hk hzk
    exact hz.2 k ((hS k).mpr hk) (C.gap_enclosed k hzk)
  have hdec := circleIntegral_eq_sum_of_finite_holes 0 R hR S c C.inner C.outer f
    (fun k _ => C.inner_pos k) (fun k _ => C.collar k) henclosed
    (fun k _ l _ hkl => C.disjoint_discs k l hkl) hhole
  have hinner (k : ℤ) : (∮ z in C(c k,C.inner k), f z) = ∮ z in C(a k,r k), f z := by
    have hC := C.contour_family
    exact sourceGapCircleIntegral_eq_of_realCentered_enclosingCircles hp hp1 k φ.val f
      (ha.mono (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val)) φ.property
      _ _ _ _ (hC.1 k) (hfamily.1 k) (hC.2 k).1 (hfamily.2 k).1
      (hC.2 k).2.1 (hfamily.2 k).2.1 (hC.2 k).2.2.1 (hfamily.2 k).2.2.1
  simpa only [hinner] using hdec

end NLS.ZakharovShabat
