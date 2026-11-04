import NLS.ComplexAnalysis.ContinuousLogarithmUnique
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- Continuous nonzero square roots with a common value agree on a
preconnected domain; no principal-root branch is selected. -/
theorem continuousSquareRoots_eqOn
    {X : Type*} [TopologicalSpace X] (F G : X → ℂ) (S : Set X)
    (hS : IsPreconnected S) (hF : ContinuousOn F S) (hG : ContinuousOn G S)
    (hGne : ∀ x∈S, G x≠0) (hsq : ∀ x∈S, (F x)^2=(G x)^2)
    (a : X) (ha : a∈S) (he : F a=G a) : EqOn F G S := by
  let T : Set ℂ := {1,-1}
  have hT : IsDiscrete T := ((finite_singleton (-1 : ℂ)).insert 1).isDiscrete
  have hc : ContinuousOn (fun x => F x/G x) S := hF.div hG hGne
  have hmaps : MapsTo (fun x => F x/G x) S T := by
    intro x hx
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq x hx) with hh | hh
    · simp only [hh,div_self (hGne x hx),T,mem_insert_iff,mem_singleton_iff,true_or]
    · simp only [hh,neg_div,div_self (hGne x hx),T,mem_insert_iff,mem_singleton_iff,or_true]
  intro x hx
  have hconst : F x/G x=F a/G a := hS.constant_of_mapsTo hT hc hmaps hx ha
  rw [he,div_self (hGne a ha)] at hconst
  exact (div_eq_one_iff_eq (hGne x hx)).mp hconst

/-- Continuous noncritical logarithmic trace primitives are uniquely
fixed by the trace and a single common value. -/
theorem continuousCoshPrimitives_eqOn
    {X : Type*} [TopologicalSpace X] (F G : X → ℂ) (S : Set X)
    (hS : IsPreconnected S) (hF : ContinuousOn F S) (hG : ContinuousOn G S)
    (htrace : ∀ x∈S, 2*cosh (F x)=2*cosh (G x))
    (hne : ∀ x∈S, 2*sinh (G x)≠0)
    (a : X) (ha : a∈S) (he : F a=G a) : EqOn F G S := by
  have hc (x : X) (hx : x∈S) : cosh (F x)=cosh (G x) :=
    mul_left_cancel₀ (by norm_num : (2 : ℂ)≠0) (htrace x hx)
  have hsquare (x : X) (hx : x∈S) : (2*sinh (F x))^2=(2*sinh (G x))^2 := by
    have h1 := cosh_sq_sub_sinh_sq (F x)
    have h2 := cosh_sq_sub_sinh_sq (G x)
    rw [hc x hx] at h1
    linear_combination -4*h1+4*h2
  have hroots := continuousSquareRoots_eqOn (fun x => 2*sinh (F x)) (fun x => 2*sinh (G x)) S hS
    ((Complex.continuous_sinh.comp_continuousOn hF).const_mul 2)
    ((Complex.continuous_sinh.comp_continuousOn hG).const_mul 2) hne hsquare a ha
    (congrArg (fun z : ℂ => 2*sinh z) he)
  apply continuousLogarithms_eqOn F G S hS hF hG _ a ha he
  intro x hx
  have hs : sinh (F x)=sinh (G x) := mul_left_cancel₀ (by norm_num : (2 : ℂ)≠0) (hroots hx)
  rw [← cosh_add_sinh,← cosh_add_sinh,hc x hx,hs]

end NLS.ComplexAnalysis
