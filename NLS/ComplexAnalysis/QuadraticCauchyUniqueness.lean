import NLS.ComplexAnalysis.QuadraticCauchyEquation
import NLS.ComplexAnalysis.FiniteProductOrders
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.LinearCombination

/-! # Uniqueness of an analytic solution of the quadratic root equation

A homogeneous solution makes the product of the quadratic polynomial
and its square constant. A contained root makes that constant zero.
The polynomial has finite analytic order everywhere, including at a
double root, so the analytic solution vanishes throughout the domain.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem quadratic_equation_homogeneous_eq_zero
    (a b : ℂ) (H : ℂ → ℂ) (Ω : Set ℂ)
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (ha : a ∈ Ω)
    (hH : AnalyticOnNhd ℂ H Ω)
    (heq : ∀ z ∈ Ω,
      quadraticRootPolynomial ((a+b)/2) ((b-a)^2/4) z*deriv H z+
        (z-(a+b)/2)*H z = 0) :
    ∀ z ∈ Ω, H z = 0 := by
  classical
  let Q := quadraticRootPolynomial ((a+b)/2) ((b-a)^2/4)
  let K : ℂ → ℂ := fun z => Q z*(H z)^2
  have hQ : AnalyticOnNhd ℂ Q univ := by
    intro z _
    unfold Q quadraticRootPolynomial
    fun_prop
  have hfactor : Q = (fun z : ℂ => a-z)*(fun z : ℂ => b-z) := by
    funext z
    dsimp only [Q,quadraticRootPolynomial,Pi.mul_apply]
    ring
  have hKa : K a = 0 := by
    dsimp only [K]
    rw [hfactor]
    simp
  have hKd (z : ℂ) (hz : z ∈ Ω) : HasDerivAt K 0 z := by
    have hh := (hH z hz).differentiableAt.hasDerivAt.pow 2
    have hd := (hasDerivAt_quadraticRootPolynomial ((a+b)/2) ((b-a)^2/4) z).fun_mul hh
    convert! hd using 1
    simp only [Pi.pow_apply]
    linear_combination -2*H z*(heq z hz)
  have hKdiff : DifferentiableOn ℂ K Ω :=
    fun z hz => (hKd z hz).differentiableAt.differentiableWithinAt
  have hKzero (z : ℂ) (hz : z ∈ Ω) : K z = 0 := by
    rw [← hKa]
    exact hΩ.is_const_of_deriv_eq_zero hconn hKdiff (fun z hz => (hKd z hz).deriv) hz ha
  intro z hz
  have hQorder : analyticOrderAt Q z ≠ ⊤ := by
    rw [hfactor,analyticOrderAt_mul (by fun_prop) (by fun_prop),
      analyticOrderAt_const_sub,analyticOrderAt_const_sub]
    split_ifs <;> norm_num
  have horder : analyticOrderAt K z = ⊤ := by
    apply analyticOrderAt_eq_top.mpr
    filter_upwards [hΩ.mem_nhds hz] with w hw
    exact hKzero w hw
  change analyticOrderAt (Q*H^2) z = ⊤ at horder
  rw [analyticOrderAt_mul (hQ z (mem_univ _)) ((hH z hz).pow 2)] at horder
  have hsquare : analyticOrderAt (H^2) z = ⊤ :=
    (ENat.add_eq_top.mp horder).resolve_left hQorder
  have he : H^2 =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := analyticOrderAt_eq_top.mp hsquare
  have hv : (H z)^2 = 0 := he.eq_of_nhds
  exact eq_zero_of_pow_eq_zero hv

end NLS.ComplexAnalysis
