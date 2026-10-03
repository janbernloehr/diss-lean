import Mathlib.Analysis.Complex.CoveringMap

/-! # Uniqueness of continuous logarithms on connected sets

A common exponential and one common value determine a continuous
logarithm on an entire connected domain. The exponential covering map
supplies the uniqueness without imposing a principal branch.
-/
open Set Complex
namespace NLS.ComplexAnalysis

/-- Continuous logarithms with the same exponential and one equal
value agree everywhere on a preconnected set. -/
theorem continuousLogarithms_eqOn
    {X : Type*} [TopologicalSpace X] (F G : X → ℂ) (S : Set X)
    (hS : IsPreconnected S) (hF : ContinuousOn F S) (hG : ContinuousOn G S)
    (hexp : ∀ x ∈ S, exp (F x) = exp (G x))
    (a : X) (ha : a ∈ S) (he : F a = G a) : EqOn F G S := by
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have hFc : Continuous (fun x : S => F x.val) := continuousOn_iff_continuous_domRestrict.mp hF
  have hGc : Continuous (fun x : S => G x.val) := continuousOn_iff_continuous_domRestrict.mp hG
  have hm : (fun z : ℂ => (⟨exp z,exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ (fun x : S => F x.val) =
      (fun z : ℂ => (⟨exp z,exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ (fun x : S => G x.val) := by
    funext x
    exact Subtype.ext (hexp x.val x.property)
  have h := isCoveringMap_exp.eq_of_comp_eq hFc hGc hm (⟨a,ha⟩ : S) he
  intro x hx
  exact congrFun h ⟨x,hx⟩

end NLS.ComplexAnalysis
