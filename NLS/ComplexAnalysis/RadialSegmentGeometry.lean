import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Outward radial connectors from a convex cut to an annulus

An outward ray from the star center of a cut cannot re-enter that cut.
Every noncentral point in a disc can reach a surrounding annulus on
this ray. Two such annular anchors are joined entirely in the annulus.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

def radialPoint (c z : ℂ) (t : ℝ) : ℂ := c+(t:ℂ)*(z-c)

@[simp] theorem radialPoint_one (c z : ℂ) : radialPoint c z 1 = z := by
  simp [radialPoint]

theorem radialPoint_mem_segment (c z : ℂ) (t u : ℝ)
    (ht : 1 ≤ t) (htu : t ≤ u) (hu : 1 < u) :
    radialPoint c z t ∈ segment ℝ z (radialPoint c z u) := by
  have hden : 0 < u-1 := sub_pos.mpr hu
  have hq : (t-1)/(u-1) ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr ht) hden.le,(div_le_one hden).mpr (by linarith)⟩
  have heq : AffineMap.lineMap z (radialPoint c z u) ((t-1)/(u-1)) = radialPoint c z t := by
    rw [AffineMap.lineMap_apply_module',Complex.real_smul]
    unfold radialPoint
    push_cast
    have hdenC : (u:ℂ)-1 ≠ 0 := by exact_mod_cast hden.ne'
    field_simp
    ring
  rw [← heq]
  exact lineMap_mem_segment ℝ _ _ hq

theorem radialPoint_not_mem_of_starConvex (c z : ℂ) (t : ℝ) (K : Set ℂ)
    (hK : StarConvex ℝ c K) (hz : z ∉ K) (ht : 1 ≤ t) :
    radialPoint c z t ∉ K := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hq : 1/t ∈ Icc (0:ℝ) 1 := ⟨(one_div_pos.mpr ht0).le,by
    simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one ht⟩
  intro hpt
  have heq : AffineMap.lineMap c (radialPoint c z t) (1/t) = z := by
    rw [AffineMap.lineMap_apply_module',Complex.real_smul]
    unfold radialPoint
    push_cast
    have htC : (t:ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    field_simp
    ring
  apply hz
  rw [← heq]
  exact hK.segment_subset hpt (lineMap_mem_segment ℝ _ _ hq)

theorem segment_radialPoint_subset_compl (c z : ℂ) (t : ℝ) (K : Set ℂ)
    (hK : StarConvex ℝ c K) (hz : z ∉ K) (ht : 1 ≤ t) :
    segment ℝ z (radialPoint c z t) ⊆ Kᶜ := by
  intro q hq
  rw [segment_eq_image_lineMap] at hq
  obtain ⟨v,hv,rfl⟩ := hq
  have heq : AffineMap.lineMap z (radialPoint c z t) v = radialPoint c z (1+v*(t-1)) := by
    rw [AffineMap.lineMap_apply_module',Complex.real_smul]
    unfold radialPoint
    push_cast
    ring
  rw [heq]
  exact radialPoint_not_mem_of_starConvex c z _ K hK hz
    (by nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr ht)])

theorem segment_radialPoint_subset_disc_compl (d c z : ℂ) (R t : ℝ) (K : Set ℂ)
    (hK : StarConvex ℝ c K) (hz : z ∈ ball d R \ K)
    (hpt : radialPoint c z t ∈ ball d R) (ht : 1 ≤ t) :
    segment ℝ z (radialPoint c z t) ⊆ ball d R \ K := by
  intro q hq
  exact ⟨(convex_ball d R).segment_subset hz.1 hpt hq,
    segment_radialPoint_subset_compl c z t K hK hz.2 ht hq⟩

theorem exists_outward_radialPoint_mem_annulus (d c z : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r < R) (hz : z ∈ ball d R) (hzc : z ≠ c) :
    ∃ t : ℝ, 1 < t ∧ radialPoint c z t ∈ ball d R \ closedBall d r := by
  let a := ‖z-c‖
  have ha : 0 < a := norm_pos_iff.mpr (sub_ne_zero.mpr hzc)
  let T := 1+(R+‖c-d‖+1)/a
  have hT : 1 < T := by
    dsimp [T]
    have hnum : 0 < R+‖c-d‖+1 := by linarith [norm_nonneg (c-d)]
    linarith [div_pos hnum ha]
  have hTa : T*a = a+R+‖c-d‖+1 := by
    dsimp [T]
    field_simp
    ring
  have hbig : R < dist (radialPoint c z T) d := by
    have htri := norm_add_le (radialPoint c z T-d) (d-c)
    have hsum : (radialPoint c z T-d)+(d-c) = (T:ℂ)*(z-c) := by
      unfold radialPoint
      ring
    rw [hsum,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < T),
      hTa,norm_sub_rev d c] at htri
    rw [dist_eq_norm]
    linarith
  let v := (max r (dist z d)+R)/2
  have hmax : max r (dist z d) < R := max_lt hrR (mem_ball.mp hz)
  have hrv : r < v := by dsimp [v]; linarith [le_max_left r (dist z d)]
  have hzv : dist z d < v := by dsimp [v]; linarith [le_max_right r (dist z d)]
  have hvR : v < R := by dsimp [v]; linarith
  have hcont : Continuous (fun t : ℝ => dist (radialPoint c z t) d) := by
    unfold radialPoint
    fun_prop
  obtain ⟨t,ht,heq⟩ := intermediate_value_Icc hT.le hcont.continuousOn
    (show v ∈ Icc (dist (radialPoint c z 1) d) (dist (radialPoint c z T) d) by
      rw [radialPoint_one]
      exact ⟨hzv.le,(hvR.trans hbig).le⟩)
  dsimp only at heq
  have ht1 : 1 < t := by
    by_contra h
    have htEq : t = 1 := le_antisymm (not_lt.mp h) ht.1
    subst t
    rw [radialPoint_one] at heq
    exact (ne_of_lt hzv) heq
  refine ⟨t,ht1,mem_ball.mpr (heq.trans_lt hvR),?_⟩
  intro h
  have hle := mem_closedBall.mp h
  rw [heq] at hle
  exact (not_le_of_gt hrv) hle

theorem segment_radialPoints_subset_annulus (d c z : ℂ) (r R t u : ℝ)
    (hc : c ∈ closedBall d r) (ht : 1 ≤ t) (hu : 1 ≤ u)
    (hat : radialPoint c z t ∈ ball d R \ closedBall d r)
    (hau : radialPoint c z u ∈ ball d R \ closedBall d r) :
    segment ℝ (radialPoint c z t) (radialPoint c z u) ⊆ ball d R \ closedBall d r := by
  have hordered (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b)
      (hpa : radialPoint c z a ∈ ball d R \ closedBall d r)
      (hpb : radialPoint c z b ∈ ball d R \ closedBall d r) :
      segment ℝ (radialPoint c z a) (radialPoint c z b) ⊆ ball d R \ closedBall d r := by
    have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
    have heq : radialPoint c (radialPoint c z a) (b/a) = radialPoint c z b := by
      unfold radialPoint
      push_cast
      have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
      field_simp
      ring
    rw [← heq]
    apply segment_radialPoint_subset_disc_compl d c _ R (b/a) (closedBall d r)
      ((convex_closedBall d r).starConvex hc) hpa (heq.symm ▸ hpb.1)
    exact (one_le_div ha0).mpr hab
  rcases le_total t u with htu | hut
  · exact hordered t u ht htu hat hau
  · rw [segment_symm]
    exact hordered u t hu hut hau hat

end NLS.ComplexAnalysis
