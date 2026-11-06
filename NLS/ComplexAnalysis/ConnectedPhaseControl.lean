import NLS.ComplexAnalysis.WeightedCoshInverse
import Mathlib.Topology.Connected.Clopen

/-! # Propagating the correct hyperbolic phase branch from one anchor

A strict local improvement turns a norm sublevel set into a clopen set.
Thus one correctly normalized anchor fixes the branch throughout a
connected parameter space. The cosh specialization retains the natural
exponential weight in its quantitative phase error.
-/

noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem norm_lt_everywhere_of_local_improvement {X E : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [SeminormedAddCommGroup E] (u : X → E) (hu : Continuous u)
    (ε : ℝ) (hlocal : ∀ x, ‖u x‖ ≤ ε → ‖u x‖ < ε)
    (x₀ : X) (hanchor : ‖u x₀‖ < ε) : ∀ x, ‖u x‖ < ε := by
  have heq : {x | ‖u x‖ < ε} = {x | ‖u x‖ ≤ ε} := by
    ext x
    change (‖u x‖ < ε) ↔ (‖u x‖ ≤ ε)
    exact ⟨fun h => h.le, hlocal x⟩
  have hclosed : IsClosed {x | ‖u x‖ < ε} := by
    rw [heq]
    exact isClosed_le hu.norm continuous_const
  have hopen : IsOpen {x | ‖u x‖ < ε} := isOpen_lt hu.norm continuous_const
  have hall := (show IsClopen {x | ‖u x‖ < ε} from ⟨hclosed, hopen⟩).eq_univ ⟨x₀, hanchor⟩
  intro x
  have hx : x ∈ {x | ‖u x‖ < ε} := by rw [hall]; exact mem_univ x
  exact hx

theorem cosh_phase_control_of_anchor {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (a u v : X → ℂ) (hu : Continuous u) (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (hεone : ε ≤ 1) (hsmall : 4*ε ≤ c)
    (ha : ∀ x, 0 ≤ (a x).re)
    (hsinh : ∀ x, c ≤ Real.exp (-(a x).re) * ‖sinh (a x)‖)
    (hv : ∀ x, ‖v x‖ ≤ ε/4)
    (htrace : ∀ x, Real.exp (-(a x).re) *
      ‖2*cosh (a x+u x) - 2*cosh (a x+v x)‖ ≤ c*ε/4)
    (x₀ : X) (hanchor : ‖u x₀‖ < ε) :
    ∀ x, ‖u x‖ < ε ∧ ‖u x-v x‖ ≤ Real.exp (-(a x).re) / c *
      ‖2*cosh (a x+u x) - 2*cosh (a x+v x)‖ := by
  have hvε (x : X) : ‖v x‖ ≤ ε := (hv x).trans (by linarith)
  have hlocal (x : X) (hx : ‖u x‖ ≤ ε) : ‖u x‖ < ε := by
    have hcomp := norm_phase_sub_le_weighted_cosh_error (a x) (u x) (v x) c ε
      (ha x) hc hεone hsmall (hsinh x) hx (hvε x)
    rw [div_mul_eq_mul_div] at hcomp
    have hdist : ‖u x-v x‖ ≤ ε/4 := hcomp.trans
      ((div_le_iff₀ hc).mpr (by nlinarith [htrace x]))
    have ht := norm_add_le (u x-v x) (v x)
    rw [sub_add_cancel] at ht
    linarith [hv x]
  have hall := norm_lt_everywhere_of_local_improvement u hu ε hlocal x₀ hanchor
  intro x
  exact ⟨hall x, norm_phase_sub_le_weighted_cosh_error (a x) (u x) (v x) c ε
    (ha x) hc hεone hsmall (hsinh x) (hall x).le (hvε x)⟩

end NLS.ComplexAnalysis
