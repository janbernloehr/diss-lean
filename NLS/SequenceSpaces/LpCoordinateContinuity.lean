import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-! Coordinate continuity with a continuous finite-exponent lp majorant.
The index type is arbitrary, including the original positive Hill labels. -/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal Classical
namespace NLS.LpSequence
variable {ι X : Type*} [TopologicalSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def truncate (s : Finset ι) (a : lp (fun _ : ι => ℂ) p) : lp (fun _ : ι => ℂ) p :=
  ∑ i ∈ s, lp.single p i (a i)

omit [Fact (1 ≤ p)] in
theorem truncate_apply (s : Finset ι) (a : lp (fun _ : ι => ℂ) p) (i : ι) :
    truncate s a i = if i ∈ s then a i else 0 := by
  classical
  change (lp.evalₗ (𝕜 := ℂ) (fun _ : ι => ℂ) p i) (∑ j ∈ s, lp.single p j (a j)) = _
  rw [map_sum]
  simp [lp.evalₗ_apply, lp.single_apply, Pi.single_apply]

theorem norm_sub_truncate_le (s : Finset ι) (a : lp (fun _ : ι => ℂ) p) :
    ‖a-truncate s a‖ ≤ ‖a‖ := by
  classical
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro i
  by_cases hi : i ∈ s <;> simp [truncate_apply,hi]

theorem continuous_truncate (s : Finset ι) : Continuous (truncate (p := p) s) := by
  unfold truncate
  exact continuous_finsetSum s (fun i _ =>
    (lp.singleContinuousLinearMap ℂ (fun _ : ι => ℂ) p i).continuous.comp
      (lp.evalCLM ℂ (fun _ : ι => ℂ) p i).continuous)

def magnitude (a : lp (fun _ : ι => ℂ) p) : lp (fun _ : ι => ℂ) p :=
  ⟨fun i => (‖a i‖:ℂ),(lp.memℓp a).mono' (by intro i; simp)⟩

theorem continuous_magnitude : Continuous (magnitude (ι := ι) (p := p)) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [dist_eq_norm,NNReal.coe_one,one_mul]
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro i
  change ‖(‖a i‖:ℂ)-(‖b i‖:ℂ)‖ ≤ ‖a i-b i‖
  simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using abs_norm_sub_norm_le (a i) (b i)

theorem continuousAt_of_coordinates_of_continuous_majorant
    (hp : p ≠ ⊤) (f g : X → lp (fun _ : ι => ℂ) p) (x : X)
    (hcoord : ∀ i, ContinuousAt (fun y => f y i) x) (hg : ContinuousAt g x)
    (hdom : ∀ᶠ y in 𝓝 x, ∀ i, ‖f y i‖ ≤ ‖g y i‖) : ContinuousAt f x := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have htr : Tendsto (fun s : Finset ι => truncate s (g x)) atTop (𝓝 (g x)) := lp.hasSum_single hp (g x)
  have ht : Tendsto (fun s : Finset ι => ‖g x-truncate s (g x)‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using ((tendsto_const_nhds (x := g x)).sub htr).norm
  obtain ⟨s,hs⟩ := (ht.eventually (gt_mem_nhds (by positivity : 0 < ε/8))).exists
  have htail : ContinuousAt (fun y => g y-truncate s (g y)) x :=
    hg.sub ((continuous_truncate s).continuousAt.comp hg)
  have htailnear : ∀ᶠ y in 𝓝 x, ‖g y-truncate s (g y)‖ < ε/4 :=
    htail.norm.eventually (gt_mem_nhds (by linarith))
  have hfin : ContinuousAt (fun y => truncate s (f y)) x := by
    clear hs htail htailnear
    induction s using Finset.induction_on with
    | empty => simpa [truncate] using (continuousAt_const : ContinuousAt (fun _ : X => (0 : lp (fun _ : ι => ℂ) p)) x)
    | @insert i s hi ih =>
      have hsingle := (lp.singleContinuousLinearMap ℂ (fun _ : ι => ℂ) p i).continuous.continuousAt.comp (hcoord i)
      change ContinuousAt (fun y => (lp.single p i (f y i) : lp (fun _ : ι => ℂ) p)) x at hsingle
      have hh := hsingle.add ih
      change ContinuousAt (fun y => (lp.single p i (f y i) : lp (fun _ : ι => ℂ) p)+truncate s (f y)) x at hh
      simpa only [truncate,Finset.sum_insert hi] using hh
  have hfinnear : ∀ᶠ y in 𝓝 x, ‖truncate s (f y)-truncate s (f x)‖ < ε/2 := by
    simpa only [dist_eq_norm] using hfin.eventually (ball_mem_nhds _ (by positivity : 0 < ε/2))
  have hdomx := mem_of_mem_nhds hdom
  have hbound (y : X) (hy : ∀ i, ‖f y i‖ ≤ ‖g y i‖) :
      ‖f y-truncate s (f y)‖ ≤ ‖g y-truncate s (g y)‖ := by
    apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    intro i
    by_cases hi : i ∈ s <;> simp [truncate_apply,hi,hy i]
  filter_upwards [hdom,htailnear,hfinnear] with y hy ht' hf'
  rw [dist_eq_norm]
  have he : f y-f x = (f y-truncate s (f y))+
      (truncate s (f y)-truncate s (f x))+(truncate s (f x)-f x) := by abel
  rw [he]
  have hlast : ‖truncate s (f x)-f x‖ < ε/8 := by
    rw [norm_sub_rev]
    exact (hbound x hdomx).trans_lt hs
  have hfirst := (hbound y hy).trans_lt ht'
  have htri := norm_add_le ((f y-truncate s (f y))+(truncate s (f y)-truncate s (f x)))
    (truncate s (f x)-f x)
  have htri' := norm_add_le (f y-truncate s (f y)) (truncate s (f y)-truncate s (f x))
  linarith

end NLS.LpSequence
