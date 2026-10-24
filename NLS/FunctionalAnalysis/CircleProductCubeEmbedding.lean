import NLS.FunctionalAnalysis.CoveringDimensionClosedSubspace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.UnitInterval
import Mathlib.Data.Fintype.EquivFin

/-! # Closed finite cubes inside infinite products of circles

Each unit interval embeds as a short circle arc. Choosing finitely many
distinct circle factors and fixing the other coordinates embeds every
finite cube as a closed subset. This gives the exact geometric input for
covering-dimension lower bounds; the cube dimension theorem is separate.
-/
noncomputable section
open Set Topology
open scoped unitInterval
namespace NLS.FunctionalAnalysis
universe u
variable {ι : Type u}

/-- Put a finite cube into selected circle factors using the short arc `exp [0,1]`. -/
def circleProductCubeMap {m : ℕ} (e : Fin m ↪ ι) (x : Fin m → unitInterval) (i : ι) : Circle := by
  classical
  exact if h : ∃ j, e j = i then Circle.exp (x h.choose) else 1

theorem circleProductCubeMap_apply_index {m : ℕ} (e : Fin m ↪ ι)
    (x : Fin m → unitInterval) (j : Fin m) :
    circleProductCubeMap e x (e j) = Circle.exp (x j) := by
  classical
  have h : ∃ k, e k = e j := ⟨j,rfl⟩
  have he : h.choose = j := e.injective h.choose_spec
  simp only [circleProductCubeMap,dif_pos h,he]

theorem continuous_circleProductCubeMap {m : ℕ} (e : Fin m ↪ ι) :
    Continuous (circleProductCubeMap e) := by
  classical
  apply continuous_pi
  intro i
  by_cases h : ∃ j, e j = i
  · simp only [circleProductCubeMap,dif_pos h]
    exact Circle.exp.continuous.comp (continuous_subtype_val.comp (continuous_apply h.choose))
  · simp only [circleProductCubeMap,dif_neg h]
    exact continuous_const

theorem circleProductCubeMap_injective {m : ℕ} (e : Fin m ↪ ι) :
    Function.Injective (circleProductCubeMap e) := by
  intro x y h
  funext j
  apply Subtype.ext
  apply Circle.exp_injOn_Icc (show (1 : ℝ)-0 < 2*Real.pi by linarith [Real.two_le_pi])
    (x j).property (y j).property
  simpa only [circleProductCubeMap_apply_index] using congrFun h (e j)

/-- Every finite collection of distinct factors contains a closed cube. -/
theorem isClosedEmbedding_circleProductCubeMap {m : ℕ} (e : Fin m ↪ ι) :
    IsClosedEmbedding (circleProductCubeMap e) :=
  (continuous_circleProductCubeMap e).isClosedEmbedding (circleProductCubeMap_injective e)

/-- An infinite circle product contains closed cubes of every finite dimension. -/
theorem exists_closedEmbedding_cube_circleProduct [Infinite ι] (m : ℕ) :
    ∃ f : (Fin m → unitInterval) → (ι → Circle), IsClosedEmbedding f := by
  let e : Fin m ↪ ι := (⟨Fin.val,Fin.val_injective⟩ : Fin m ↪ ℕ).trans (Infinite.natEmbedding ι)
  exact ⟨circleProductCubeMap e,isClosedEmbedding_circleProductCubeMap e⟩

/-- Every finite covering-dimension bound on the infinite product bounds all finite cubes. -/
theorem HasCoveringDimensionLE.cube_of_circleProduct [Infinite ι] {n : ℕ}
    (h : HasCoveringDimensionLE (ι → Circle) n) (m : ℕ) :
    HasCoveringDimensionLE (Fin m → unitInterval) n := by
  obtain ⟨f,hf⟩ := exists_closedEmbedding_cube_circleProduct (ι := ι) m
  exact h.of_isClosedEmbedding hf

end NLS.FunctionalAnalysis
