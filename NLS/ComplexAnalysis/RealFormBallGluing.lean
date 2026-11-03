import NLS.ComplexAnalysis.ContinuousRealFormIdentity
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! # Gluing analytic maps on balls centered in a real form

Intersecting real-centered balls contain a real point on the segment of
their centers. The real-form identity theorem propagates real agreement
to the whole complex overlap. The union domain is independent of the
local scalar or Banach-valued functions being glued.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem exists_real_mem_ball_inter (R : Set E) (hR : Convex ℝ R)
    (a b : E) (r s : ℝ) (ha : a ∈ R) (hb : b ∈ R)
    (h : (ball a r ∩ ball b s).Nonempty) :
    ∃ c ∈ ball a r ∩ ball b s, c ∈ R := by
  obtain ⟨z,hza,hzb⟩ := h
  have hr : 0 < r := dist_nonneg.trans_lt hza
  have hs : 0 < s := dist_nonneg.trans_lt hzb
  have hrs : 0 < r+s := add_pos hr hs
  have hd : dist a b < r+s := by
    calc
      dist a b ≤ dist a z+dist z b := dist_triangle _ _ _
      _ < r+s := add_lt_add (by simpa only [mem_ball,dist_comm] using hza) hzb
  let t := r/(r+s)
  have ht : 0 < t := div_pos hr hrs
  have ht1 : t < 1 := (div_lt_one hrs).mpr (by linarith)
  have htr : t*(r+s) = r := div_mul_cancel₀ r (ne_of_gt hrs)
  have hts : (1-t)*(r+s) = s := by nlinarith [htr]
  refine ⟨AffineMap.lineMap a b t,⟨?_,?_⟩,?_⟩
  · change dist (AffineMap.lineMap a b t) a < r
    rw [dist_lineMap_left,Real.norm_of_nonneg ht.le]
    exact (mul_lt_mul_of_pos_left hd ht).trans_eq htr
  · change dist (AffineMap.lineMap a b t) b < s
    rw [dist_lineMap_right,Real.norm_of_nonneg (by linarith : 0 ≤ 1-t)]
    exact (mul_lt_mul_of_pos_left hd (by linarith : 0 < 1-t)).trans_eq hts
  · exact hR.segment_subset ha hb (lineMap_mem_segment ℝ a b ⟨ht.le,ht1.le⟩)

theorem eqOn_ball_inter_of_continuous_real_form_agreement
    (R : Set E) (hR : Convex ℝ R)
    (hRadd : ∀ ⦃x y : E⦄, x ∈ R → y ∈ R → x+y ∈ R)
    (hRsmul : ∀ (t : ℝ) ⦃x : E⦄, x ∈ R → (t : ℂ) • x ∈ R)
    (A B : E → E) (hAR : ∀ v, A v ∈ R) (hBR : ∀ v, B v ∈ R)
    (hdecomp : ∀ v, v = A v+Complex.I • B v)
    (hA : ContinuousAt A 0) (hA0 : A 0 = 0) (hB : ContinuousAt B 0) (hB0 : B 0 = 0)
    (f g : E → F) (a b : E) (r s : ℝ) (ha : a ∈ R) (hb : b ∈ R)
    (hf : AnalyticOnNhd ℂ f (ball a r)) (hg : AnalyticOnNhd ℂ g (ball b s))
    (he : ∀ c ∈ ball a r ∩ ball b s, c ∈ R → f c = g c) :
    EqOn f g (ball a r ∩ ball b s) := by
  by_cases h : (ball a r ∩ ball b s).Nonempty
  · obtain ⟨c,hc,hcR⟩ := exists_real_mem_ball_inter R hR a b r s ha hb h
    have hz := AnalyticOnNhd.eqOn_zero_of_continuous_real_form R hRadd hRsmul A B hAR hBR
      hdecomp hA hA0 hB hB0 (ball a r ∩ ball b s) (isOpen_ball.inter isOpen_ball)
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected ⟨c,hc,hcR⟩ (f-g)
      ((hf.mono inter_subset_left).sub (hg.mono inter_subset_right))
      (fun z hz hr => sub_eq_zero.mpr (he z hz hr))
    exact fun z hzU => sub_eq_zero.mp (hz hzU)
  · intro z hz
    exact (h ⟨z,hz⟩).elim

theorem exists_analyticOnNhd_gluing_continuous_real_form
    (R : Set E) (hR : Convex ℝ R)
    (hRadd : ∀ ⦃x y : E⦄, x ∈ R → y ∈ R → x+y ∈ R)
    (hRsmul : ∀ (t : ℝ) ⦃x : E⦄, x ∈ R → (t : ℂ) • x ∈ R)
    (A B : E → E) (hAR : ∀ v, A v ∈ R) (hBR : ∀ v, B v ∈ R)
    (hdecomp : ∀ v, v = A v+Complex.I • B v)
    (hA : ContinuousAt A 0) (hA0 : A 0 = 0) (hB : ContinuousAt B 0) (hB0 : B 0 = 0)
    {ι : Type*} (a : ι → E) (r : ι → ℝ) (f : ι → E → F)
    (ha : ∀ i, a i ∈ R) (hf : ∀ i, AnalyticOnNhd ℂ (f i) (ball (a i) (r i)))
    (he : ∀ i j c, c ∈ ball (a i) (r i) ∩ ball (a j) (r j) → c ∈ R → f i c = f j c) :
    ∃ G : E → F, AnalyticOnNhd ℂ G (⋃ i, ball (a i) (r i)) ∧
      (∀ i, EqOn G (f i) (ball (a i) (r i))) ∧
      (∀ H : E → F, (∀ i, EqOn H (f i) (ball (a i) (r i))) → EqOn H G (⋃ i, ball (a i) (r i))) := by
  classical
  have hcompat (i j : ι) : EqOn (f i) (f j) (ball (a i) (r i) ∩ ball (a j) (r j)) :=
    eqOn_ball_inter_of_continuous_real_form_agreement R hR hRadd hRsmul A B hAR hBR hdecomp
      hA hA0 hB hB0 (f i) (f j) (a i) (a j) (r i) (r j) (ha i) (ha j) (hf i) (hf j) (he i j)
  let G : E → F := fun z => if hz : ∃ i, z ∈ ball (a i) (r i) then f hz.choose z else 0
  have hG (i : ι) : EqOn G (f i) (ball (a i) (r i)) := by
    intro z hz
    have hex : ∃ j, z ∈ ball (a j) (r j) := ⟨i,hz⟩
    dsimp only [G]
    rw [dif_pos hex]
    exact hcompat hex.choose i ⟨hex.choose_spec,hz⟩
  refine ⟨G,?_,hG,?_⟩
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    apply (hf i z hi).congr
    filter_upwards [isOpen_ball.mem_nhds hi] with w hw
    exact (hG i hw).symm
  · intro H hH z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact (hH i hi).trans (hG i hi).symm

end NLS.ComplexAnalysis
