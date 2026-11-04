import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.CompactOpen

/-! # Continuous parameter families of original periodic physical functions

Joint continuity descends through the spatial quotient and gives continuity
in the circle's compact-open topology, hence in its uniform function norm.
-/
noncomputable section
set_option autoImplicit false
open Topology
namespace NLS.FunctionalAnalysis
variable {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]

theorem continuous_periodic_lift_family (L : ℝ) (f : P → ℝ → B)
    (hp : ∀ a, Function.Periodic (f a) L)
    (hc : Continuous (fun z : P × ℝ => f z.1 z.2)) :
    Continuous (fun z : P × AddCircle L => (hp z.1).lift z.2) := by
  have hq : IsOpenQuotientMap (fun z : P × ℝ => (z.1,(z.2 : AddCircle L))) :=
    IsOpenQuotientMap.id.prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples L))
  exact hq.continuous_comp_iff.mp hc

def periodicContinuousFamily (L : ℝ) (f : P → ℝ → B)
    (hp : ∀ a, Function.Periodic (f a) L)
    (hc : Continuous (fun z : P × ℝ => f z.1 z.2)) : P → C(AddCircle L,B) := fun a =>
  ⟨(hp a).lift,(continuous_periodic_lift_family L f hp hc).comp
    (continuous_const.prodMk continuous_id)⟩

@[simp] theorem periodicContinuousFamily_apply (L : ℝ) (f : P → ℝ → B)
    (hp : ∀ a, Function.Periodic (f a) L)
    (hc : Continuous (fun z : P × ℝ => f z.1 z.2)) (a : P) (x : ℝ) :
    periodicContinuousFamily L f hp hc a (x : AddCircle L) = f a x := rfl

theorem continuous_periodicContinuousFamily (L : ℝ) (f : P → ℝ → B)
    (hp : ∀ a, Function.Periodic (f a) L)
    (hc : Continuous (fun z : P × ℝ => f z.1 z.2)) :
    Continuous (periodicContinuousFamily L f hp hc) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_periodic_lift_family L f hp hc)

end NLS.FunctionalAnalysis
