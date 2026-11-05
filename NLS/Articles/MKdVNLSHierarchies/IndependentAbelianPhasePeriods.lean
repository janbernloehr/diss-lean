import NLS.MKdV.MiuraFiniteGapPhaseTerminalRegularity

/-! # Independent Abelian normalization on the original physical action circles

The exact period and the source orientation are checked. The resulting
negative generators are proved at interior finite-gap divisors. The full
finite-gap phase is differentiable even at terminal configurations, but
the canonical generator there and arbitrary-support rotation remain open.
-/
noncomputable section
open Set Metric Complex NLS.KdV NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem independent_Abelian_original_action_circle_normalization (a : ScalarDomain 2)
    (ha : ∀ k,a.val k = conj (a.val (-k))) (W : Set (CoeffPair 2))
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (hφ : (realDiagonalH1Source a ha).val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (j : ℕ) (hj : 1 ≤ j) (r : ℝ) (hr : C.discs.inner j ≤ r ∧ r < C.discs.outer j)
    (n : ℕ) (hn : 1 ≤ n) :
    let q := realSobolevMiuraHillPotential a ha
    (∮ z in C(C.discs.center j,r),z*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn (z^2)/
      sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) z) =
        (Real.pi:ℂ)*(if j = n then 1 else 0) :=
  miuraSelectedAbelianPsi_original_circle_period a ha W C hφ j hj r hr n hn

theorem independent_source_oriented_phase_finite_gap_generator
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hnF : n-1 ∈ F) (t : ℝ)
    (hclosed : ∀ k, k ∉ F → hillRealGapHalfLength (miuraNativeHillActionCurve s hs a j t).val
      (miuraNativeHillActionCurve s hs a j t).property.1 (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) = 0)
    (hR : ∀ k ∈ F,hillDirichletSheetRoot
      (SpectralWeight.one.toCoeff (miuraNativeHillActionCurve s hs a j t).val)
      (hillDirichletEnergy (miuraNativeHillActionCurve s hs a j t).val
        (miuraNativeHillActionCurve s hs a j t).property.1
        (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) (by omega)) ≠ 0) :
    HasDerivAt (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r))
      (-I*(if j = n then 1 else 0)*miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)) t :=
  hasDerivAt_miuraNativeOppositeAbelianPhase_actionFlow_finiteGap_generator s hs a j hj n hn F hnF t hclosed hR

theorem independent_source_oriented_phase_finite_gap_terminal_regularity
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (t : ℝ)
    (hclosed : ∀ k,k ∉ F → hillRealGapHalfLength (miuraNativeHillActionCurve s hs a j t).val
      (miuraNativeHillActionCurve s hs a j t).property.1
      (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) = 0) :
    DifferentiableAt ℝ (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r)) t :=
  differentiableAt_miuraNativeOppositeAbelianPhase_actionFlow_finiteGap s hs a j hj n hn F t hclosed

theorem independent_source_oriented_phase_native_data
    (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (miuraNativeOppositeAbelianPhase s hs n hn) {a | miuraNativeNLSAngularCoordinate s n a ≠ 0} ∧
      (∀ a,‖miuraNativeOppositeAbelianPhase s hs n hn a‖ ≤ 1) ∧
      (∀ a,miuraNativeNLSAngularCoordinate s n a ≠ 0 → ‖miuraNativeOppositeAbelianPhase s hs n hn a‖ = 1) ∧
      (∀ a,miuraNativeNLSAngularCoordinate s n a = 0 → miuraNativeOppositeAbelianPhase s hs n hn a = 0) :=
  ⟨continuousOn_miuraNativeOppositeAbelianPhase s hs n hn,
    norm_miuraNativeOppositeAbelianPhase_le_one s hs n hn,
    norm_miuraNativeOppositeAbelianPhase s hs n hn,miuraNativeOppositeAbelianPhase_closed s hs n hn⟩

end NLS.Articles.MKdVNLSHierarchies
