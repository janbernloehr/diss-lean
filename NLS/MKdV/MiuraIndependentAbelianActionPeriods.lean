import NLS.MKdV.MiuraCauchyCircleBands
import NLS.MKdV.MiuraIndependentCanonicalRoot
import NLS.KdV.HillSquaredCirclePeriods

/-! # Exact independent Abelian periods on the original physical action circles

Squaring supplies the literal Jacobian two. The independent Hill root
agrees with the physical root on the whole homotopy domain. The actual
frequency period is pi times the Kronecker delta, with positive sign,
for every original real H1 profile and every positive indexed circle.
-/
noncomputable section
open Set Metric Complex MeasureTheory NLS.ComplexAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval
namespace NLS.MKdV

theorem miuraSelectedAbelianPsi_original_circle_period (a : ScalarDomain 2)
    (ha : ∀ k,a.val k = conj (a.val (-k))) (W : Set (CoeffPair 2))
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (hφ : (realDiagonalH1Source a ha).val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (j : ℕ) (hj : 1 ≤ j) (r : ℝ) (hr : C.discs.inner j ≤ r ∧ r < C.discs.outer j)
    (n : ℕ) (hn : 1 ≤ n) :
    let q := realSobolevMiuraHillPotential a ha
    (∮ z in C(C.discs.center j,r),z*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn (z^2)/
      sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) z) =
        (Real.pi:ℂ)*(if j = n then 1 else 0) := by
  let q := realSobolevMiuraHillPotential a ha
  let c := (C.discs.center j).re
  let d := hillRealGapCenter q.val q.property.1 q.property.2 j
  let R := hillRealGapHalfLength q.val q.property.1 q.property.2 j+hillRealGapCollar q.val q.property.1 q.property.2 j
  have hc : (c : ℂ) = C.discs.center j :=
    Complex.ext rfl (by simpa only [ofReal_im] using (C.discs.center_real j).symm)
  have hr0 : 0 < r := (C.discs.inner_pos j).trans_le hr.1
  have hrc : r < c := by
    have hp := (miuraCauchy_circle_real_band_bounds a ha W C hφ j hj r hr).1
    change 0 < c-r at hp
    linarith
  have hb := miuraCauchy_squared_circle_band_bounds a ha W C hφ j hj r hr
  obtain ⟨hR,hleft,hright⟩ := hillIntrinsicCircle_band_crossings q.val q.property.1 q.property.2 j hj
  have hroot (θ : ℝ) :
      hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 ((circleMap (c:ℂ) r θ)^2) =
        sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) (circleMap (c:ℂ) r θ) := by
    let z := circleMap (c:ℂ) r θ
    have he := lineMap_squared_circle_mem_real_bands c r d R
      (hillRealLabels q.val q.property.1 q.property.2 (2*j-2)) (hillRealLabels q.val q.property.1 q.property.2 (2*j-1))
      (hillRealLabels q.val q.property.1 q.property.2 (2*j)) (hillRealLabels q.val q.property.1 q.property.2 (2*j+1))
      hr0 hrc hR hb.1 hleft hb.2 hright 0 θ
    have hzcut : z^2 ∈ hillL2RealCutDomain q.val q.property.1 q.property.2 := by
      simp only [show ((0:I):ℝ) = 0 from rfl,AffineMap.lineMap_apply_zero] at he
      exact hillTwoBands_subset_realCutDomain q.val q.property.1 q.property.2 j hj _ he
    have hzball : z ∈ closedBall (c:ℂ) r := circleMap_mem_closedBall _ hr0.le _
    have hzright : 0 < z.re := re_pos_on_closedBall_of_radius_lt_re (by simpa only [ofReal_re] using hrc) z hzball
    have hzroot : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (realDiagonalH1Source a ha).val := by
      apply C.intermediate_circle_root j _ hφ r hr.1 hr.2
      rw [← hc]
      exact circleMap_mem_sphere _ hr0.le _
    exact (hillEnergyCanonicalRootProduct_eq_canonicalMiuraHillRoot a ha hzcut).trans
      (canonicalMiuraHillSheets_eq_NLS a ha z hzright hzroot).1
  have hint : (∮ z in C((c:ℂ),r),z*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn (z^2)/
      sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) z) =
      ∮ z in C((c:ℂ),r),z*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn (z^2)/
        hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 (z^2) := by
    unfold circleIntegral
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [hroot θ]
  rw [← hc]
  exact hint.trans (hillSelectedPsi_squared_circle_period q.val q.property.1 q.property.2 j hj c r hr0 hrc hb.1 hb.2 n hn)

end NLS.MKdV
