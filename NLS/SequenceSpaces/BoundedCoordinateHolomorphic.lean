import NLS.SequenceSpaces.Truncation
import Mathlib.Analysis.Complex.Schwarz

/-!
# Norm continuity from bounded holomorphic coordinates

For a finite exponent, a locally bounded map into `ℓq` with complex
differentiable scalar coordinates is norm-continuous. Finite Fourier
truncations are holomorphic, and the Schwarz estimate bounds their
variation independently of the truncation. Passing to the norm limit
gives the same estimate for the full sequence map.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every finite truncation of a coordinatewise complex-differentiable
sequence map is complex-differentiable on the same open domain. -/
theorem differentiableOn_truncate_of_coordinatewise
    (f : E → Coeff q) {V : Set E} (hVopen : IsOpen V)
    (hcoord : ∀ n : ℤ, DifferentiableOn ℂ (fun x => f x n) V)
    (s : Finset ℤ) :
    DifferentiableOn ℂ (fun x => truncate s (f x)) V := by
  induction s using Finset.induction_on with
  | empty =>
      simpa only [truncate_empty] using (differentiableOn_const (c := (0 : Coeff q)) :
        DifferentiableOn ℂ (fun _ : E => (0 : Coeff q)) V)
  | @insert n s hn ih =>
      have hsingle : DifferentiableOn ℂ
          (fun x : E => (lp.single q n (f x n) : Coeff q)) V := by
        intro x hx
        have hcx : DifferentiableAt ℂ (fun y : E => f y n) x :=
          (hcoord n x hx).differentiableAt (hVopen.mem_nhds hx)
        have hmap : DifferentiableAt ℂ
          (fun z : ℂ => (lp.single q n z : Coeff q)) (f x n) :=
          (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) q n).differentiableAt
        exact (hmap.comp x hcx).differentiableWithinAt
      have heq : (fun x : E => truncate (insert n s) (f x)) =
          (fun x : E => (lp.single q n (f x n) : Coeff q) + truncate s (f x)) := by
        funext x
        simp only [truncate,Finset.sum_insert hn]
      rw [heq]
      exact hsingle.add ih

/-- A uniform local norm bound and coordinatewise holomorphy give a
source Lipschitz estimate at each point, independent of finite
truncations. -/
theorem exists_local_norm_sub_le_of_bounded_coordinatewise
    (hq : q ≠ ⊤) (f : E → Coeff q) {V : Set E}
    (hVopen : IsOpen V)
    (hcoord : ∀ n : ℤ, DifferentiableOn ℂ (fun x => f x n) V)
    (M : ℝ) (hbound : ∀ x ∈ V, ‖f x‖ ≤ M)
    (c : E) (hc : c ∈ V) :
    ∃ R : ℝ, 0 < R ∧ ball c R ⊆ V ∧
      ∀ y ∈ ball c R, ‖f y - f c‖ ≤ (2*M/R)*‖y-c‖ := by
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hVopen c hc
  refine ⟨R,hR,hball,?_⟩
  intro y hy
  have hM : 0 ≤ M := (norm_nonneg (f c)).trans (hbound c hc)
  have hlimit : Tendsto
      (fun s : Finset ℤ => ‖truncate s (f y) - truncate s (f c)‖)
      atTop (𝓝 ‖f y-f c‖) :=
    ((tendsto_truncate hq (f y)).sub (tendsto_truncate hq (f c))).norm
  apply le_of_tendsto hlimit
  apply Filter.Eventually.of_forall
  intro s
  let g : E → Coeff q := fun x => truncate s (f x)
  have hg : DifferentiableOn ℂ g (ball c R) :=
    (differentiableOn_truncate_of_coordinatewise f hVopen hcoord s).mono hball
  have hgnorm (x : E) (hx : x ∈ ball c R) : ‖g x‖ ≤ M :=
    (norm_truncate_le (ne_of_gt (zero_lt_one.trans_le Fact.out)) s (f x)).trans
      (hbound x (hball hx))
  have hmaps : MapsTo g (ball c R) (closedBall (g c) (2*M)) := by
    intro x hx
    rw [mem_closedBall,dist_eq_norm]
    calc
      ‖g x-g c‖ ≤ ‖g x‖+‖g c‖ := norm_sub_le _ _
      _ ≤ M+M := add_le_add (hgnorm x hx) (hgnorm c (mem_ball_self hR))
      _ = 2*M := by ring
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hmaps hy
  simpa only [g,dist_eq_norm] using hs

/-- Bounded coordinatewise holomorphic maps into finite `ℓq` are
continuous in their sequence norm. -/
theorem continuousOn_of_bounded_coordinatewise
    (hq : q ≠ ⊤) (f : E → Coeff q) {V : Set E}
    (hVopen : IsOpen V)
    (hcoord : ∀ n : ℤ, DifferentiableOn ℂ (fun x => f x n) V)
    (M : ℝ) (hbound : ∀ x ∈ V, ‖f x‖ ≤ M) :
    ContinuousOn f V := by
  intro c hc
  obtain ⟨R,hR,_,hLip⟩ :=
    exists_local_norm_sub_le_of_bounded_coordinatewise hq f hVopen hcoord M hbound c hc
  have hcont : ContinuousAt (fun y : E => (2*M/R)*‖y-c‖) c := by fun_prop
  have hfc : ContinuousAt f c := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hnear : ∀ᶠ y : E in 𝓝 c, (2*M/R)*‖y-c‖ < ε :=
      hcont.eventually (gt_mem_nhds (by simpa using hε))
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR),hnear] with y hy hsmall
    rw [dist_eq_norm]
    exact (hLip y hy).trans_lt hsmall
  exact hfc.continuousWithinAt

end NLS.Coeff
