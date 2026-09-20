import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Locally uniform limits in analytic families

Joint continuity gives compact-open continuity in the spectral variable.
For entire fibers, the locally uniform limit theorem transfers this
continuity to the spectral derivative.
-/

noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

/-- A jointly continuous complex family varies locally uniformly in the spectral parameter. -/
theorem tendstoLocallyUniformlyOn_of_joint_continuous {A : Type*} [TopologicalSpace A]
    (f : A → ℂ → ℂ) (hf : Continuous (Function.uncurry f)) (a : A) :
    TendstoLocallyUniformlyOn f (f a) (𝓝 a) Set.univ := by
  let F : A → C(ℂ,ℂ) := fun b => ⟨f b,hf.comp (continuous_const.prodMk continuous_id)⟩
  have hc : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F hf
  exact (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hc.continuousAt).tendstoLocallyUniformlyOn

/-- Derivatives of entire fibers inherit locally uniform parameter continuity. -/
theorem tendstoLocallyUniformlyOn_deriv_of_joint_continuous {A : Type*} [TopologicalSpace A]
    (f : A → ℂ → ℂ) (hf : Continuous (Function.uncurry f))
    (ha : ∀ a, Differentiable ℂ (f a)) (a : A) :
    TendstoLocallyUniformlyOn (fun b => deriv (f b)) (deriv (f a)) (𝓝 a) Set.univ :=
  (tendstoLocallyUniformlyOn_of_joint_continuous f hf a).deriv
    (Eventually.of_forall (fun b => (ha b).differentiableOn)) isOpen_univ

end NLS.ComplexAnalysis
