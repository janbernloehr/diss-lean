import NLS.ComplexAnalysis.UnitSquareRootComparison
import NLS.SequenceSpaces.LocallyUniformCoordinates
import NLS.SequenceSpaces.PowerDecaySummability
import NLS.SequenceSpaces.FiniteExponentTail
import NLS.SequenceSpaces.FiniteHeadTailBound
import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.SequenceSpaces.FourierTail

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [TopologicalSpace E]

omit [Fact (1 ≤ p)] in
/-- A continuous square-root family with uniformly small squared tails preserves
the normalized lp branch throughout a preconnected set. -/
theorem memlp_root_error_on_preconnected
    (hp : p ≠ ⊤) (hp1 : 1 < p) {U : Set E} (hU : IsPreconnected U)
    (f : E → ℤ → ℂ) (hf : ∀ n, ContinuousOn (fun x => f x n) U)
    (e : E → Coeff p) (he : ∀ x ∈ U, ∀ n, e x n = (f x n)^2-1)
    (K : ℕ) (hsmall : ∀ x ∈ U, ∀ n, K < n.natAbs → ‖e x n‖ < 1)
    (a : E) (ha : a ∈ U) (hbase : Memℓp (fun n => f a n-1) p) :
    ∀ x ∈ U, Memℓp (fun n => f x n-1) p := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  let b : Coeff p := ⟨_,hbase⟩
  obtain ⟨N,hN⟩ := exists_natAbs_norm_lt hpr b (by norm_num : 0 < (1:ℝ)/2)
  intro x hx
  have hbound (n : ℤ) (hn : max (K+1) N ≤ n.natAbs) : ‖f x n-1‖ ≤ ‖e x n‖ := by
    have hnK : K < n.natAbs := by omega
    have hnN : N ≤ n.natAbs := (le_max_right _ _).trans hn
    have hnear : ‖f a n-1‖ < 1/2 := hN n hnN
    have hpos : 0 < (f a n).re := by
      have h := (neg_le_abs (f a n-1).re).trans (Complex.abs_re_le_norm (f a n-1))
      simp only [sub_re,one_re] at h
      linarith
    have hbnd := norm_sub_one_le_sq_sub_one_on_preconnected hU (fun y => f y n) (hf n)
      a ha hpos (fun y hy => by rw [← he y hy n]; exact hsmall y hy n hnK) x hx
    simpa only [← he x hx n] using hbnd
  have hm := memlp_of_natAbs_eventual_bound p.toReal hpr (fun n => f x n-1)
    (fun n => ‖e x n‖) (by simpa only [ENNReal.ofReal_toReal hp] using (lp.memℓp (e x)).norm)
    (max (K+1) N) hbound
  simpa only [ENNReal.ofReal_toReal hp] using hm


section Normed
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Continuity of the squared-error sequence propagates the normalized root branch
from one base point to every point of an open preconnected domain. -/
theorem memlp_root_error_on_open_preconnected
    (hp : p ≠ ⊤) (hp1 : 1 < p) {W : Set X} (hW : IsOpen W) (hconn : IsPreconnected W)
    (f : X → ℤ → ℂ) (hf : ∀ n, ContinuousOn (fun x => f x n) W)
    (e : X → Coeff p) (hec : ContinuousOn e W)
    (he : ∀ x ∈ W, ∀ n, e x n = (f x n)^2-1)
    (a : X) (ha : a ∈ W) (hbase : Memℓp (fun n => f a n-1) p) :
    ∀ x ∈ W, Memℓp (fun n => f x n-1) p := by
  have hlocal (x : X) (hx : x ∈ W) :
      ∃ r : ℝ, 0 < r ∧ ball x r ⊆ W ∧
        ∀ y ∈ ball x r, Memℓp (fun n => f y n-1) p →
          ∀ z ∈ ball x r, Memℓp (fun n => f z n-1) p := by
    obtain ⟨K,V,hV,hxV,hsmall⟩ := exists_local_uniform_small_coordinates hp e x
      ((hec x hx).continuousAt (hW.mem_nhds hx)) 1 (by norm_num)
    obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp ((hW.inter hV).mem_nhds ⟨hx,hxV⟩)
    refine ⟨r,hr,fun y hy => (hrsub hy).1,?_⟩
    intro y hy hygood
    exact memlp_root_error_on_preconnected hp hp1 (convex_ball x r).isPreconnected
      f (fun n => (hf n).mono (fun z hz => (hrsub hz).1)) e
      (fun z hz => he z (hrsub hz).1) K
      (fun z hz => hsmall z (hrsub hz).2) y hy hygood
  let S : Set X := {x | x ∈ W ∧ Memℓp (fun n => f x n-1) p}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨hx,hgood⟩
    obtain ⟨r,hr,hrsub,hprop⟩ := hlocal x hx
    apply Filter.mem_of_superset (ball_mem_nhds x hr)
    intro y hy
    exact ⟨hrsub hy,hprop x (mem_ball_self hr) hgood y hy⟩
  have hclosed : closure S ∩ W ⊆ S := by
    rintro x ⟨hxcl,hxW⟩
    obtain ⟨r,hr,hrsub,hprop⟩ := hlocal x hxW
    obtain ⟨y,hyS,hxy⟩ := Metric.mem_closure_iff.mp hxcl r hr
    have hy : y ∈ ball x r := by simpa only [mem_ball,dist_comm] using hxy
    exact ⟨hxW,hprop y hy hyS.2 x (mem_ball_self hr)⟩
  have hWS : W ⊆ S := hconn.subset_of_closure_inter_subset hS ⟨a,ha,ha,hbase⟩ hclosed
  exact fun x hx => (hWS hx).2

end Normed


section LocalBounds
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The normalized root error has locally bounded lp norm at every normalized base point. -/
theorem exists_local_root_error_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) {W : Set X} (hW : IsOpen W)
    (f : X → ℤ → ℂ) (hf : ∀ n, ContinuousOn (fun x => f x n) W)
    (e : X → Coeff p) (hec : ContinuousOn e W)
    (he : ∀ x ∈ W, ∀ n, e x n = (f x n)^2-1)
    (a : X) (ha : a ∈ W) (hbase : Memℓp (fun n => f a n-1) p) :
    ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ V ⊆ W ∧ ∃ B : ℝ,
      ∀ x ∈ V, Memℓp (fun n => f x n-1) p ∧
        ‖ofFunctionOrZero p (fun n => f x n-1)‖ ≤ B := by
  classical
  have hecont := (hec a ha).continuousAt (hW.mem_nhds ha)
  obtain ⟨K,T,hT,haT,hsmall⟩ := exists_local_uniform_small_coordinates hp e a hecont 1 (by norm_num)
  have heb : ∀ᶠ x in 𝓝 a, ‖e x‖ < ‖e a‖+1 := hecont.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((hW.inter hT).mem_nhds ⟨ha,haT⟩) heb)
  let U := ball a r
  have haU : a ∈ U := mem_ball_self hr
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  let b : Coeff p := ⟨_,hbase⟩
  obtain ⟨N,hN⟩ := exists_natAbs_norm_lt hpr b (by norm_num : 0 < (1:ℝ)/2)
  let L := max (K+1) N
  have htail (x : X) (hx : x ∈ U) (n : ℤ) (hn : L ≤ n.natAbs) :
      ‖f x n-1‖ ≤ ‖e x n‖ := by
    have hnK : K < n.natAbs := by dsimp only [L] at hn; omega
    have hnN : N ≤ n.natAbs := (le_max_right _ _).trans hn
    have hnear : ‖f a n-1‖ < 1/2 := hN n hnN
    have hpos : 0 < (f a n).re := by
      have h := (neg_le_abs (f a n-1).re).trans (Complex.abs_re_le_norm (f a n-1))
      simp only [sub_re,one_re] at h
      linarith
    have hbnd := norm_sub_one_le_sq_sub_one_on_preconnected (convex_ball a r).isPreconnected
      (fun y => f y n) ((hf n).mono (fun y hy => (hrsub hy).1.1)) a haU hpos
      (fun y hy => by rw [← he y (hrsub hy).1.1 n]; exact hsmall y (hrsub hy).1.2 n hnK) x hx
    simpa only [← he x (hrsub hx).1.1 n] using hbnd
  let S := lowFrequencies L
  let head : X → Coeff p := fun x => finiteHead S (fun n => f x n-1)
  have hh : ContinuousAt head a := by
    unfold head finiteHead
    apply tendsto_finsetSum S
    intro n _
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n).continuous.continuousAt.comp
      (((hf n a ha).continuousAt (hW.mem_nhds ha)).sub continuousAt_const)
  have hhb : ∀ᶠ x in 𝓝 a, ‖head x‖ < ‖head a‖+1 :=
    hh.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨V,hVsub,hV,haV⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (ball_mem_nhds a hr) hhb)
  refine ⟨V,hV,haV,fun x hx => (hrsub (hVsub hx).1).1.1,
    (‖head a‖+1)+(‖e a‖+1),?_⟩
  intro x hx
  obtain ⟨hm,hbnd⟩ := memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound
    (fun n => f x n-1) (fun n => f x n-1) S (e x) 0 1 (by norm_num)
    (fun _ _ => le_rfl) (by
      intro n hn
      have hnL : L ≤ n.natAbs := by
        simpa only [S,mem_lowFrequencies,not_lt] using hn
      simpa only [lp.coeFn_zero,Pi.zero_apply,norm_zero,add_zero,one_mul] using
        htail x (hVsub hx).1 n hnL)
  refine ⟨hm,hbnd.trans ?_⟩
  change ‖head x‖+1*(‖e x‖+‖(0 : Coeff p)‖) ≤ _
  simp only [norm_zero,add_zero,one_mul]
  have hhead : ‖head x‖ < ‖head a‖+1 := (hVsub hx).2
  have hnorm : ‖e x‖ < ‖e a‖+1 := (hrsub (hVsub hx).1).2
  exact add_le_add hhead.le hnorm.le

end LocalBounds

section Analytic
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Scalar analytic roots with an analytic lp squared error have an analytic
normalized lp error on a connected domain once the branch is fixed at one point. -/
theorem analytic_normalized_root_error
    (hp : p ≠ ⊤) (hp1 : 1 < p) {W : Set X} (hW : IsOpen W) (hconn : IsPreconnected W)
    (f : X → ℤ → ℂ) (hf : ∀ n, AnalyticOnNhd ℂ (fun x => f x n) W)
    (e : X → Coeff p) (hec : ContinuousOn e W)
    (he : ∀ x ∈ W, ∀ n, e x n = (f x n)^2-1)
    (a : X) (ha : a ∈ W) (hbase : Memℓp (fun n => f a n-1) p) :
    AnalyticOnNhd ℂ (fun x => ofFunctionOrZero p (fun n => f x n-1)) W ∧
      ∀ x ∈ W, ∀ n, ofFunctionOrZero p (fun n => f x n-1) n = f x n-1 := by
  have hm := memlp_root_error_on_open_preconnected hp hp1 hW hconn f
    (fun n => (hf n).continuousOn) e hec he a ha hbase
  obtain ⟨hv,hg⟩ := analytic_realization_of_local_bounds (fun x n => f x n-1) hW
    (fun n => (hf n).sub analyticOnNhd_const) (by
      intro x hx
      obtain ⟨V,hV,hxV,hVW,B,hb⟩ := exists_local_root_error_bound hp hp1 hW f
        (fun n => (hf n).continuousOn) e hec he x hx (hm x hx)
      refine ⟨V,hV,hxV,hVW,B,?_⟩
      intro y hy
      exact ⟨ofFunctionOrZero p (fun n => f y n-1),
        ofFunctionOrZero_apply_of_mem p _ (hb y hy).1,(hb y hy).2⟩)
  exact ⟨hg,hv⟩

end Analytic

end NLS.Coeff
