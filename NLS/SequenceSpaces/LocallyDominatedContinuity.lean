import NLS.SequenceSpaces.UniformTailContinuity

/-! # Continuity under a local tail majorant

Coordinatewise continuity becomes lp norm continuity when a locally uniform
coordinate majorant has uniformly small tails. The majorant itself need not
be continuous, which permits use of unordered spectral gap lengths.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {X : Type*} [TopologicalSpace X]

/-- A local coordinate majorant with uniformly small lp tails transfers norm continuity. -/
theorem continuousAt_of_coordinatewise_of_locally_dominated_tails
    (f g : X → Coeff p) (x : X)
    (hcoord : ∀ n : ℤ, ContinuousAt (fun y => f y n) x)
    (V : Set X) (hV : IsOpen V) (hxV : x ∈ V) (C : ℝ) (hC : 0 < C)
    (hdom : ∀ y ∈ V, ∀ n : ℤ, ‖f y n‖ ≤ C * ‖g y n‖)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ s : Finset ℤ, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, ‖g y-truncate s (g y)‖ ≤ ε) :
    ContinuousAt f x := by
  apply continuousAt_of_coordinatewise_of_uniform_tails f x hcoord
  intro ε hε
  obtain ⟨s, U, hU, hxU, hbound⟩ := htail (ε/C) (div_pos hε hC)
  refine ⟨s, V ∩ U, hV.inter hU, ⟨hxV, hxU⟩, ?_⟩
  intro y hy
  have h : ‖f y-truncate s (f y)‖ ≤ ‖(C : ℂ) • (g y-truncate s (g y))‖ := by
    apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    intro n
    by_cases hn : n ∈ s
    · simp [truncate_apply, hn]
    · simpa only [lp.coeFn_sub, Pi.sub_apply, truncate_apply, if_neg hn, sub_zero,
        lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hC] using hdom y hy.1 n
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (hbound y hy.2) hC.le).trans_eq
    (mul_div_cancel₀ ε hC.ne'))

end NLS.Coeff
