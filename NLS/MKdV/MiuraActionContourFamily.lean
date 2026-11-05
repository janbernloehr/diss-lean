import NLS.MKdV.MiuraLaurentContourComparison
import NLS.ComplexAnalysis.PiecewiseSquareWinding

/-! # Genuine positive-gap contours for every original real H¹ profile

The checked all-index Cauchy family supplies actual isolating circles.
For a diagonal source every positive circle excludes zero and lies in
the right half-plane. Its squared image is a physical Hill contour with
winding one at its indexed gap, zero at other positive gaps and at zero.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

structure MiuraActionContourFamily (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) where
  domain : Set (CoeffPair 2)
  cauchy : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) domain
  source_eq : cauchy.discs.source = realDiagonalH1Source a ha

theorem nonempty_miuraActionContourFamily (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) : Nonempty (MiuraActionContourFamily a ha) := by
  obtain ⟨W,_,_,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  obtain ⟨C,hCφ⟩ := hC (realDiagonalH1Source a ha)
  exact ⟨⟨W,C,hCφ⟩⟩

def miuraActionContourFamily (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) :
    MiuraActionContourFamily a ha := Classical.choice (nonempty_miuraActionContourFamily a ha)

namespace MiuraActionContourFamily
variable {a : ScalarDomain 2} {ha : ∀ n, a.val n = conj (a.val (-n))} (F : MiuraActionContourFamily a ha)

theorem source_mem : (realDiagonalH1Source a ha).val ∈
    ball F.cauchy.discs.source.val F.cauchy.discs.sourceRadius := by
  rw [F.source_eq]
  exact mem_ball_self F.cauchy.discs.sourceRadius_pos

def radius (n : ℤ) : ℝ := (F.cauchy.discs.inner n+F.cauchy.discs.outer n)/2

def frequencyContour (n : ℤ) : PiecewiseC1Loop := PiecewiseC1Loop.circle (F.cauchy.discs.center n) (F.radius n)
def energyContour (n : ℤ) : PiecewiseC1Loop := (F.frequencyContour n).square

theorem radius_bounds (n : ℤ) : F.cauchy.discs.inner n ≤ F.radius n ∧ F.radius n < F.cauchy.discs.outer n := by
  dsimp only [radius]
  constructor <;> linarith [F.cauchy.discs.inner_lt n]

theorem radius_pos (n : ℤ) : 0 < F.radius n := (F.cauchy.discs.inner_pos n).trans_le (F.radius_bounds n).1

theorem circle_rootDomain (n : ℤ) : sphere (F.cauchy.discs.center n) (F.radius n) ⊆
    sourceCanonicalRootDomain (by simp) (by norm_num) (realDiagonalH1Source a ha).val :=
  F.cauchy.intermediate_circle_root n _ F.source_mem _ (F.radius_bounds n).1 (F.radius_bounds n).2

theorem zero_mem_central_segment : (0 : ℂ) ∈
    sourcePeriodicSegment (by simp) (by norm_num) (realDiagonalH1Source a ha).val 0 := by
  apply sourcePeriodicSegment_mem_of_realIcc _ _ _ (realDiagonalH1Source a ha).property 0 0
  have h := congrArg Complex.re (miuraNLSEndpoints_reflection a 0).1
  simp only [neg_zero,neg_re] at h
  have hR := miuraNLSRight_zero_nonnegative a
  change (miuraNLSLeft a 0).re ≤ 0 ∧ 0 ≤ (miuraNLSRight a 0).re
  exact ⟨by linarith,hR⟩

theorem zero_not_mem_outer (n : ℕ) (hn : 1 ≤ n) :
    (0 : ℂ) ∉ closedBall (F.cauchy.discs.center n) (F.cauchy.discs.outer n) := by
  intro h0
  exact F.cauchy.discs.avoids_other _ F.source_mem n h0 0 (by omega) (zero_mem_central_segment (a := a) (ha := ha))

theorem outer_radius_lt_center_re (n : ℕ) (hn : 1 ≤ n) :
    F.cauchy.discs.outer n < (F.cauchy.discs.center n).re := by
  have hL : ((miuraNLSLeft a n).re : ℂ) = miuraNLSLeft a n :=
    Complex.ext rfl (by simpa only [ofReal_im] using (miuraNLSEndpoints_real a ha n).1.symm)
  apply radius_lt_re_of_zero_excluded (F.cauchy.discs.center_real n) (F.zero_not_mem_outer n hn)
    (miuraNLSLeft_pos a ha (show (0 : ℤ) < n by omega))
  rw [hL]
  exact (ball_subset_ball (F.cauchy.discs.inner_lt n).le)
    (F.cauchy.discs.segment_subset _ F.source_mem n (left_mem_segment ℝ _ _))

theorem outer_disc_right (n : ℕ) (hn : 1 ≤ n) :
    ∀ z ∈ closedBall (F.cauchy.discs.center n) (F.cauchy.discs.outer n), 0 < z.re :=
  re_pos_on_closedBall_of_radius_lt_re (F.outer_radius_lt_center_re n hn)

theorem frequencyContour_inside (n : ℕ) (hn : 1 ≤ n) :
    (F.frequencyContour n).Inside (miuraRightFrequencyDomain a) := by
  apply PiecewiseC1Loop.circle_inside_of_sphere_subset _ _ (F.radius_pos n).le
  intro z hz
  exact ⟨F.outer_disc_right n hn (z := z)
    (closedBall_subset_closedBall (F.radius_bounds n).2.le (sphere_subset_closedBall hz)),
    F.circle_rootDomain n hz⟩

theorem energyContour_inside (n : ℕ) (hn : 1 ≤ n) :
    (F.energyContour n).Inside (miuraHillGapComplement a ha) :=
  miuraSquaredContour_inside a ha _ (F.frequencyContour_inside n hn)

theorem opposite_not_mem_circle_disc (n : ℕ) (hn : 1 ≤ n) (w : ℂ) (hw : 0 ≤ w.re) :
    -w ∉ closedBall (F.cauchy.discs.center n) (F.radius n) := by
  intro hm
  have h := F.outer_disc_right n hn (-w)
    (closedBall_subset_closedBall (F.radius_bounds n).2.le hm)
  simp only [neg_re] at h
  linarith

theorem energyContour_winding_gap (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re) :
    (F.energyContour n).windingIntegral ((x : ℂ)^2) = 1 := by
  have hxmem := sourcePeriodicSegment_mem_of_realIcc (by simp) (by norm_num)
    (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property n x hx
  have hball : (x : ℂ) ∈ ball (F.cauchy.discs.center n) (F.radius n) :=
    ball_subset_ball (F.radius_bounds n).1 (F.cauchy.discs.segment_subset _ F.source_mem n hxmem)
  have hxpos : 0 < x := (miuraNLSLeft_pos a ha (show (0 : ℤ) < n by omega)).trans_le hx.1
  exact PiecewiseC1Loop.windingIntegral_square_circle_of_mem_ball _ _ _ (F.radius_pos n).le hball
    (F.opposite_not_mem_circle_disc n hn x hxpos.le)

theorem energyContour_winding_other_gap (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n)
    (x : ℝ) (hx : x ∈ Icc (miuraNLSLeft a m).re (miuraNLSRight a m).re) :
    (F.energyContour n).windingIntegral ((x : ℂ)^2) = 0 := by
  have hxmem := sourcePeriodicSegment_mem_of_realIcc (by simp) (by norm_num)
    (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property m x hx
  have hout : (x : ℂ) ∉ closedBall (F.cauchy.discs.center n) (F.radius n) := by
    intro hc
    exact F.cauchy.discs.avoids_other _ F.source_mem n
      (closedBall_subset_closedBall (F.radius_bounds n).2.le hc) m (by exact_mod_cast hmn) hxmem
  have hxpos : 0 < x := (miuraNLSLeft_pos a ha (show (0 : ℤ) < m by omega)).trans_le hx.1
  exact PiecewiseC1Loop.windingIntegral_square_circle_of_not_mem_closedBall _ _ _
    (F.radius_pos n).le hout (F.opposite_not_mem_circle_disc n hn x hxpos.le)

theorem energyContour_winding_zero (n : ℕ) (hn : 1 ≤ n) : (F.energyContour n).windingIntegral 0 = 0 := by
  have h0 : (0 : ℂ) ∉ closedBall (F.cauchy.discs.center n) (F.radius n) := by
    intro hm
    exact F.zero_not_mem_outer n hn (closedBall_subset_closedBall (F.radius_bounds n).2.le hm)
  simpa only [energyContour,frequencyContour,zero_pow (by decide : 2 ≠ 0)] using
    PiecewiseC1Loop.windingIntegral_square_circle_of_not_mem_closedBall
      (F.cauchy.discs.center n) 0 (F.radius n) (F.radius_pos n).le h0 (by simpa only [neg_zero] using h0)

end MiuraActionContourFamily
end NLS.MKdV
