import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Normed.Module.Connected

/-! # The circle has no contraction

The real exponential covering would admit a continuous lift of the identity
if the circle were simply connected. Uniqueness of lifts would then make
that lift invert the periodic exponential on the whole real line.
-/
noncomputable section
open Set Topology
namespace NLS.FunctionalAnalysis

/-- Periodicity of the exponential covering obstructs simple connectedness of the circle. -/
theorem not_simplyConnectedSpace_circle : ¬ SimplyConnectedSpace Circle := by
  intro h
  let := h
  let : LocallyPathConnectedSpace ℝ := LocallyPathConnectedSpace.of_bases
    (fun x : ℝ => Metric.nhds_basis_ball)
    (fun x r hr => (convex_ball x r).isPathConnected ⟨x,Metric.mem_ball_self hr⟩)
  let : LocallyPathConnectedSpace Circle :=
    (Circle.isCoveringMap_exp.isLocalHomeomorph.isOpenMap.isQuotientMap
      Circle.exp.continuous (fun z => ⟨(z : ℂ).arg, Circle.exp_arg z⟩)).locallyPathConnectedSpace
  obtain ⟨F,hF,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    (ContinuousMap.id Circle) 1 0 (by simp)
  have he : (fun x : ℝ => F (Circle.exp x)) = id := by
    refine Circle.isCoveringMap_exp.eq_of_comp_eq
      (F.continuous.comp Circle.exp.continuous) continuous_id ?_ (0 : ℝ) ?_
    · funext x
      exact congrFun hF.2 (Circle.exp x)
    · simpa using hF.1
  have hperiod := congrFun he (2*Real.pi)
  have hz := congrFun he 0
  have hp : Circle.exp (2*Real.pi) = Circle.exp 0 := by
    simp
  rw [hp] at hperiod
  dsimp only [id] at hz hperiod
  have : (2 : ℝ)*Real.pi = 0 := hperiod.symm.trans hz
  exact (mul_ne_zero (by norm_num) Real.pi_ne_zero) this

/-- The unit circle is not contractible. -/
theorem not_contractibleSpace_circle : ¬ ContractibleSpace Circle := by
  intro h
  let := h
  exact not_simplyConnectedSpace_circle inferInstance

end NLS.FunctionalAnalysis
