import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot
import Mathlib.Topology.Algebra.Field
import Mathlib.Tactic.FieldSimp

/-!
# Continuous square roots along paths

Two continuous nonzero square roots of the same scalar function differ
by one fixed sign on a connected parameter set. A continuous nonzero
root of a differentiable square is differentiable along the real
parameter, without any globally prescribed analytic chart.
-/

noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- A continuous choice of square root has one fixed relative sign
on a connected set where the reference root never vanishes. -/
theorem exists_fixed_sign_of_sq_eq_on_preconnected
    {X : Type*} [TopologicalSpace X] (f g : X → ℂ) (S : Set X)
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : ∀ x ∈ S, f x^2 = g x^2) (hne : ∀ x ∈ S, g x ≠ 0) :
    ∃ κ : ℂ, (κ = 1 ∨ κ = -1) ∧ ∀ x ∈ S, f x = κ*g x := by
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg hsq (fun {x} hx => hne x hx) with h | h
  · exact ⟨1,Or.inl rfl,fun x hx => by simpa only [one_mul] using h hx⟩
  · exact ⟨-1,Or.inr rfl,fun x hx => by simpa only [neg_one_mul,Pi.neg_apply] using h hx⟩

/-- The local prescribed root at the current value recovers the
derivative of a continuous real-parameter root from its square. -/
theorem hasDerivAt_continuous_root_of_sq
    (r : ℝ → ℂ) (x u : ℂ) (t : ℝ)
    (hr : ContinuousAt r t) (hx : r t = x) (hne : x ≠ 0)
    (hsq : HasDerivAt (fun v => r v^2) u t) :
    HasDerivAt r (u/(2*x)) t := by
  let g : ℝ → ℂ := prescribedSquareRoot (fun v => r v^2) x
  have hbase : g t = r t := by
    exact (prescribedSquareRoot_base _ _ hne t (by rw [hx])).trans hx.symm
  have hratio : r t^2/x^2 = 1 := by rw [hx]; exact div_self (pow_ne_zero 2 hne)
  have hsqrt : HasDerivAt Complex.sqrt (1/2 : ℂ) (r t^2/x^2) := by
    rw [hratio]
    simpa only [one_cpow] using Complex.hasDerivAt_sqrt
      (show (1:ℂ) ∈ slitPlane by simp [Complex.mem_slitPlane_iff])
  have hd := (hsqrt.scomp t (hsq.div_const (x^2))).const_mul x
  have hd' : HasDerivAt g (u/(2*x)) t := by
    convert! hd using 1
    convert_to! u/(2*x) = x*((u/x^2)*(1/2))
    field_simp [hne]
  have heq : r =ᶠ[𝓝 t] g :=
    (eventuallyEq_of_sq_eq_of_continuousAt g r t hd'.continuousAt hr hbase
      (by rwa [hx]) (Eventually.of_forall fun v => prescribedSquareRoot_sq _ _ hne v)).symm
  exact hd'.congr_of_eventuallyEq heq

end NLS.ComplexAnalysis
