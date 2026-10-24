import NLS.ZakharovShabat.L2WholeLineModeNotL2
import NLS.ZakharovShabat.FloquetQuadraticReduction

/-! # No nonzero whole-line physical fundamental solution is globally L2 -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix
namespace NLS.ZakharovShabat

theorem l2WholeLineSolution_sub_smul (u : IntervalPairL2) (z ν : ℂ)
    (v w : Fin 2 → ℂ) (t : ℝ) :
    l2WholeLineSolution u z (v-ν • w) t =
      l2WholeLineSolution u z v t-ν • l2WholeLineSolution u z w t := by
  simp only [l2WholeLineSolution,Matrix.mulVec_sub,Matrix.mulVec_smul,
    Pi.sub_apply,Pi.smul_apply,Prod.smul_mk,Prod.mk_sub_mk]

/-- Applying the actual monodromy to initial data shifts the solution by one period. -/
theorem l2WholeLineSolution_monodromy (u : IntervalPairL2) (z : ℂ)
    (v : Fin 2 → ℂ) (t : ℝ) :
    l2WholeLineSolution u z (l2Monodromy u z *ᵥ v) t =
      l2WholeLineSolution u z v (t+1) := by
  have he := l2WholeLineFundamentalMatrix_add_int u z t 1
  simp only [Int.cast_one,zpow_one,coe_l2MonodromyUnit] at he
  simp only [l2WholeLineSolution,he,Matrix.mulVec_mulVec]

/-- The characteristic-quadratic reduction excludes global L2 solutions
even at repeated roots, without assuming a Floquet eigenbasis. -/
theorem not_memLp_l2WholeLineSolution (u : IntervalPairL2) (z : ℂ)
    (v : Fin 2 → ℂ) (hv : v ≠ 0) : ¬ MemLp (l2WholeLineSolution u z v) 2 volume := by
  intro hF
  let M := l2Monodromy u z
  obtain ⟨μ,ν,hμ,hν,hsum,hprod⟩ := exists_reciprocal_roots_with_sum M.trace
  have hdet : M.det = μ*ν := (det_l2Monodromy u z).trans hprod.symm
  let w := M *ᵥ v-ν • v
  have hw : M *ᵥ w = μ • w := mulVec_sub_smul_eigenvector_of_two_roots M μ ν hsum hdet v
  have hW : MemLp (l2WholeLineSolution u z w) 2 volume := by
    have hshift := hF.comp_measurePreserving (measurePreserving_add_right volume (1 : ℝ))
    have he : l2WholeLineSolution u z w =
        fun t => l2WholeLineSolution u z v (t+1)-ν • l2WholeLineSolution u z v t := by
      funext t
      rw [l2WholeLineSolution_sub_smul,l2WholeLineSolution_monodromy]
    rw [he]
    exact hshift.sub (hF.const_smul ν)
  have hw0 : w = 0 := by
    by_contra hn
    exact not_memLp_l2WholeLineSolution_of_floquet u z μ hμ w hn hw hW
  have hvν : M *ᵥ v = ν • v := sub_eq_zero.mp hw0
  exact not_memLp_l2WholeLineSolution_of_floquet u z ν hν v hv hvν hF

end NLS.ZakharovShabat
