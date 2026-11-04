import NLS.MKdV.MiuraActionContourFamily
import NLS.MKdV.MiuraHillDirichletPositivity
import NLS.ComplexAnalysis.OrderedRealGapCircleBounds
import NLS.KdV.HillRealGapContourDiscs

/-! # Actual Laurent frequency circles cross adjacent Hill bands after squaring

The original all-index isolating discs supply every endpoint bound. The
central gap is included in the lower band at index one, for any signed
mean and with no open-gap assumption.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraCauchy_circle_real_band_bounds (a : ScalarDomain 2)
    (ha : ∀ k,a.val k = conj (a.val (-k))) (W : Set (CoeffPair 2))
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (hφ : (realDiagonalH1Source a ha).val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (j : ℕ) (hj : 1 ≤ j) (r : ℝ) (hr : C.discs.inner j ≤ r ∧ r < C.discs.outer j) :
    0 < (C.discs.center j).re-r ∧
      (C.discs.center j).re-r ∈ Ioo (miuraNLSRight a ((j:ℤ)-1)).re (miuraNLSLeft a j).re ∧
      (C.discs.center j).re+r ∈ Ioo (miuraNLSRight a j).re (miuraNLSLeft a ((j:ℤ)+1)).re := by
  have hc : ((C.discs.center j).re : ℂ) = C.discs.center j :=
    Complex.ext rfl (by simpa only [ofReal_im] using (C.discs.center_real j).symm)
  have hL (k : ℤ) : ((miuraNLSLeft a k).re : ℂ) = miuraNLSLeft a k :=
    Complex.ext rfl (by simpa only [ofReal_im] using (miuraNLSEndpoints_real a ha k).1.symm)
  have hR (k : ℤ) : ((miuraNLSRight a k).re : ℂ) = miuraNLSRight a k :=
    Complex.ext rfl (by simpa only [ofReal_im] using (miuraNLSEndpoints_real a ha k).2.symm)
  have hleft : miuraNLSLeft a j ∈ ball (C.discs.center j) r :=
    ball_subset_ball hr.1 (C.discs.segment_subset _ hφ j (left_mem_segment ℝ _ _))
  have hright : miuraNLSRight a j ∈ ball (C.discs.center j) r :=
    ball_subset_ball hr.1 (C.discs.segment_subset _ hφ j (right_mem_segment ℝ _ _))
  have hprev : miuraNLSRight a ((j:ℤ)-1) ∉ closedBall (C.discs.center j) r := by
    intro hz
    exact C.discs.avoids_other _ hφ j (closedBall_subset_closedBall hr.2.le hz) _ (by omega)
      (right_mem_segment ℝ _ _)
  have hnext : miuraNLSLeft a ((j:ℤ)+1) ∉ closedBall (C.discs.center j) r := by
    intro hz
    exact C.discs.avoids_other _ hφ j (closedBall_subset_closedBall hr.2.le hz) _ (by omega)
      (left_mem_segment ℝ _ _)
  have hzero : (0:ℂ) ∉ closedBall (C.discs.center j) r := by
    intro hz
    exact C.discs.avoids_other _ hφ j (closedBall_subset_closedBall hr.2.le hz) 0 (by omega)
      (MiuraActionContourFamily.zero_mem_central_segment (a := a) (ha := ha))
  have hp : r < (C.discs.center j).re := radius_lt_re_of_zero_excluded (C.discs.center_real j) hzero
    (miuraNLSLeft_pos a ha (show (0:ℤ) < j by omega)) (by rwa [hL])
  refine ⟨by linarith,?_⟩
  apply ordered_real_gap_circle_bounds (C.discs.center j).re r
    (miuraNLSRight a ((j:ℤ)-1)).re (miuraNLSLeft a j).re
    (miuraNLSRight a j).re (miuraNLSLeft a ((j:ℤ)+1)).re
  · rwa [hc,hL]
  · rwa [hc,hR]
  · rwa [hc,hR]
  · rwa [hc,hL]
  · exact (miuraNLSEndpoints_between a ha (show (j:ℤ)-1 < j by omega)).le
  · exact (miuraNLSEndpoints_between a ha (show (j:ℤ) < (j:ℤ)+1 by omega)).le

theorem miuraHillLabels_even (a : ScalarDomain 2)
    (ha : ∀ k,a.val k = conj (a.val (-k))) (j : ℕ) :
    miuraHillLabels a ha (2*j) = (miuraNLSRight a j).re^2 := by
  by_cases hj : j = 0
  · subst j
    exact miuraHillLabels_ground a ha
  · exact miuraHillLabels_right a ha j (by omega)

theorem miuraCauchy_squared_circle_band_bounds (a : ScalarDomain 2)
    (ha : ∀ k,a.val k = conj (a.val (-k))) (W : Set (CoeffPair 2))
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (hφ : (realDiagonalH1Source a ha).val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (j : ℕ) (hj : 1 ≤ j) (r : ℝ) (hr : C.discs.inner j ≤ r ∧ r < C.discs.outer j) :
    let q := realSobolevMiuraHillPotential a ha
    ((C.discs.center j).re-r)^2 ∈ Ioo (hillRealLabels q.val q.property.1 q.property.2 (2*j-2))
      (hillRealLabels q.val q.property.1 q.property.2 (2*j-1)) ∧
    ((C.discs.center j).re+r)^2 ∈ Ioo (hillRealLabels q.val q.property.1 q.property.2 (2*j))
      (hillRealLabels q.val q.property.1 q.property.2 (2*j+1)) := by
  obtain ⟨hp,hl,hu⟩ := miuraCauchy_circle_real_band_bounds a ha W C hφ j hj r hr
  have hprev0 : 0 ≤ (miuraNLSRight a ((j:ℤ)-1)).re := by
    by_cases he : j = 1
    · simpa only [he,Nat.cast_one,sub_self] using miuraNLSRight_zero_nonnegative a
    · exact (miuraNLSLeft_pos a ha (show (0:ℤ) < (j:ℤ)-1 by omega)).le.trans
        (miuraNLSEndpoints_within a ((j:ℤ)-1))
  have hcur0 : 0 ≤ (miuraNLSRight a j).re :=
    (miuraNLSLeft_pos a ha (show (0:ℤ) < j by omega)).le.trans (miuraNLSEndpoints_within a j)
  have hr0 : 0 < r := (C.discs.inner_pos j).trans_le hr.1
  have heprev : miuraHillLabels a ha (2*j-2) = (miuraNLSRight a ((j:ℤ)-1)).re^2 := by
    have he := miuraHillLabels_even a ha (j-1)
    simpa only [show 2*(j-1) = 2*j-2 by omega,Nat.cast_sub hj,Nat.cast_one] using he
  have henext : miuraHillLabels a ha (2*j+1) = (miuraNLSLeft a ((j:ℤ)+1)).re^2 := by
    have he := miuraHillLabels_left a ha (j+1) (by omega)
    simpa only [show 2*(j+1)-1 = 2*j+1 by omega,Nat.cast_add,Nat.cast_one] using he
  change ((C.discs.center j).re-r)^2 ∈ Ioo (miuraHillLabels a ha (2*j-2)) (miuraHillLabels a ha (2*j-1)) ∧
    ((C.discs.center j).re+r)^2 ∈ Ioo (miuraHillLabels a ha (2*j)) (miuraHillLabels a ha (2*j+1))
  rw [heprev,miuraHillLabels_left a ha j hj,miuraHillLabels_right a ha j hj,henext]
  constructor <;> constructor <;> nlinarith [hl.1,hl.2,hu.1,hu.2]

end NLS.MKdV
