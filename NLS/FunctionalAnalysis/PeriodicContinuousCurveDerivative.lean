import NLS.FunctionalAnalysis.ContinuousMapCurveDerivative
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Algebra.Ring.Periodic

/-! Periodic jointly continuous scalar fields as curves in the uniform norm.
Joint continuity descends through the open circle quotient. A jointly
continuous pointwise time derivative is the actual Banach derivative. -/
noncomputable section
namespace NLS.FunctionalAnalysis

local instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

def periodicContinuousCircle (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f 2) : C(AddCircle (2 : ℝ), ℂ) :=
  ⟨hp.lift, continuous_coinduced_dom.mpr hf⟩

@[simp] theorem periodicContinuousCircle_coe (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f 2) (x : ℝ) :
    periodicContinuousCircle f hf hp (x : AddCircle (2 : ℝ)) = f x := rfl

theorem continuous_periodicContinuousCircle
    (f : ℝ × ℝ → ℂ) (hf : Continuous f)
    (hp : ∀ t, Function.Periodic (fun x => f (t, x)) 2) :
    Continuous (fun t => periodicContinuousCircle (fun x => f (t, x))
      (hf.comp (continuous_const.prodMk continuous_id)) (hp t)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  rw [← (IsOpenQuotientMap.id.prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (2 : ℝ)))).continuous_comp_iff]
  exact hf

theorem hasDerivAt_periodicContinuousCircle
    (f g : ℝ × ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hpf : ∀ t, Function.Periodic (fun x => f (t, x)) 2)
    (hpg : ∀ t, Function.Periodic (fun x => g (t, x)) 2)
    (hd : ∀ t x, HasDerivAt (fun s => f (s, x)) (g (t, x)) t) (t : ℝ) :
    HasDerivAt (fun s => periodicContinuousCircle (fun x => f (s, x))
      (hf.comp (continuous_const.prodMk continuous_id)) (hpf s))
      (periodicContinuousCircle (fun x => g (t, x))
        (hg.comp (continuous_const.prodMk continuous_id)) (hpg t)) t := by
  apply hasDerivAt_continuousMap_of_pointwise _ _
    (continuous_periodicContinuousCircle g hg hpg)
  intro s x
  induction x using Quotient.inductionOn with
  | h x => exact hd s x

end NLS.FunctionalAnalysis
