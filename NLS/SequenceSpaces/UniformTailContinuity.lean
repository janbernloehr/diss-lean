import NLS.SequenceSpaces.Truncation

/-!
# Continuity from coordinates and locally uniform tails

For finite sequence exponents, coordinatewise continuity alone does
not imply continuity in the `ℓp` norm. A locally uniform finite-tail
bound supplies the missing control. This criterion will be used for
the critical-root displacement sequence.
-/

open Filter Topology Metric
open scoped ENNReal
noncomputable section

namespace NLS.Coeff

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {X : Type*} [TopologicalSpace X]

/-- A finite truncation of a coordinatewise continuous coefficient map
is continuous in the sequence norm. -/
theorem continuousAt_truncate_of_coordinatewise
    (f : X → Coeff p) (x : X) (s : Finset ℤ)
    (hcoord : ∀ n : ℤ, ContinuousAt (fun y => f y n) x) :
    ContinuousAt (fun y => truncate s (f y)) x := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using (continuousAt_const : ContinuousAt
        (fun _ : X => (0 : Coeff p)) x)
  | @insert n s hn ih =>
      have hsingle : ContinuousAt
          (fun y : X => (lp.single p n (f y n) : Coeff p)) x := by
        change ContinuousAt
          (fun y : X => (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n)
            (f y n)) x
        exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n).continuous.continuousAt.comp
          (f := fun y : X => f y n) (hcoord n)
      have heq : (fun y : X => truncate (insert n s) (f y)) =
          (fun y : X => lp.single p n (f y n) + truncate s (f y)) := by
        funext y
        simp only [truncate, Finset.sum_insert hn]
      rw [heq]
      exact hsingle.add ih

/-- Locally uniform finite tails upgrade coordinatewise continuity to
norm continuity of an `ℓp`-valued map. -/
theorem continuousAt_of_coordinatewise_of_uniform_tails
    (f : X → Coeff p) (x : X)
    (hcoord : ∀ n : ℤ, ContinuousAt (fun y => f y n) x)
    (htail : ∀ ε : ℝ, 0 < ε →
      ∃ s : Finset ℤ, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, ‖f y - truncate s (f y)‖ ≤ ε) :
    ContinuousAt f x := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s,V,hVopen,hxV,hbound⟩ := htail (ε/4) (by positivity)
  have hfin := continuousAt_truncate_of_coordinatewise f x s hcoord
  have hfinNear : ∀ᶠ y : X in 𝓝 x,
      dist (truncate s (f y)) (truncate s (f x)) < ε/2 :=
    hfin.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [hVopen.mem_nhds hxV,hfinNear] with y hyV hyfin
  rw [dist_eq_norm] at hyfin ⊢
  have hbase := hbound x hxV
  have hy := hbound y hyV
  have hdecomp : f y - f x =
      (f y - truncate s (f y)) +
        (truncate s (f y) - truncate s (f x)) +
          (truncate s (f x) - f x) := by abel
  rw [hdecomp]
  have hlast : ‖truncate s (f x) - f x‖ ≤ ε/4 := by
    simpa only [norm_sub_rev] using hbase
  have htri := norm_add_le
    ((f y - truncate s (f y)) +
      (truncate s (f y) - truncate s (f x)))
    (truncate s (f x) - f x)
  have htri' := norm_add_le (f y - truncate s (f y))
    (truncate s (f y) - truncate s (f x))
  linarith

end NLS.Coeff
