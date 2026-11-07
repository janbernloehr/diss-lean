import NLS.ZakharovShabat.DiscriminantFloquetAlgebra
import NLS.ZakharovShabat.L2DiscriminantXiIntegral
import NLS.ZakharovShabat.L2WholeLineIntegralEquation

/-! # Whole-line physical gradients, scalar transport and periodicity

The actual physical L2 fundamental matrix defines the gradient continuation
at every real spatial point. It agrees with the actual Fréchet gradient on
the unit interval. Determinant-one Floquet transport proves period one;
the original rough ODE proves the spatial identities almost everywhere.
-/
noncomputable section
open Set Complex Matrix MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

def l2WholeLineDiscriminantGradient (u : IntervalPairL2) (z : ℂ) (x : ℝ) : ℂ × ℂ :=
  discriminantGradientMatrix (l2Monodromy u z) (l2WholeLineFundamentalMatrix u z x)

def l2WholeLineDiscriminantXi (u : IntervalPairL2) (z : ℂ) (x : ℝ) : ℂ :=
  discriminantXiMatrix (l2Monodromy u z) (l2WholeLineFundamentalMatrix u z x)

private theorem columns_eq_solution (u : IntervalPairL2) (z : ℂ) (x : ℝ) :
    ((l2WholeLineFundamentalMatrix u z x) 0 0,(l2WholeLineFundamentalMatrix u z x) 1 0) =
        l2WholeLineSolution u z ![1,0] x ∧
    ((l2WholeLineFundamentalMatrix u z x) 0 1,(l2WholeLineFundamentalMatrix u z x) 1 1) =
        l2WholeLineSolution u z ![0,1] x := by
  simp [l2WholeLineSolution,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem l2WholeLineDiscriminantGradient_eq_state (u : IntervalPairL2) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantGradient u z x = discriminantGradientState (l2Monodromy u z)
      (l2WholeLineSolution u z ![1,0] x) (l2WholeLineSolution u z ![0,1] x) := by
  unfold l2WholeLineDiscriminantGradient discriminantGradientMatrix
  rw [(columns_eq_solution u z x).1,(columns_eq_solution u z x).2]

theorem l2WholeLineDiscriminantXi_eq_state (u : IntervalPairL2) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantXi u z x = discriminantXiState (l2Monodromy u z)
      (l2WholeLineSolution u z ![1,0] x) (l2WholeLineSolution u z ![0,1] x) := by
  unfold l2WholeLineDiscriminantXi discriminantXiMatrix
  rw [(columns_eq_solution u z x).1,(columns_eq_solution u z x).2]

theorem l2WholeLineDiscriminantGradient_on_unit (u : IntervalPairL2) (z : ℂ)
    (x : Icc (0:ℝ) 1) :
    l2WholeLineDiscriminantGradient u z x = l2DiscriminantGradient u z x := by
  have hs (v : Fin 2 → ℂ) : l2WholeLineSolution u z v x = l2SolutionCurve u z (v 0,v 1) x := by
    simpa only [Int.cast_zero,add_zero,_root_.zpow_zero,Units.val_one,Matrix.one_mulVec]
      using l2WholeLineSolution_on_period u z v 0 x
  rw [l2WholeLineDiscriminantGradient_eq_state,hs,hs,← extend_coe,← extend_coe]
  exact (l2DiscriminantGradient_eq_state u z x).symm

theorem periodic_l2WholeLineDiscriminantGradient (u : IntervalPairL2) (z : ℂ) :
    Function.Periodic (l2WholeLineDiscriminantGradient u z) 1 := by
  intro x
  unfold l2WholeLineDiscriminantGradient
  have h := l2WholeLineFundamentalMatrix_add_int u z x 1
  simp only [Int.cast_one,_root_.zpow_one,coe_l2MonodromyUnit] at h
  rw [h,discriminantGradientMatrix_mul,det_l2Monodromy,one_smul]

theorem periodic_l2WholeLineDiscriminantXi (u : IntervalPairL2) (z : ℂ) :
    Function.Periodic (l2WholeLineDiscriminantXi u z) 1 := by
  intro x
  unfold l2WholeLineDiscriminantXi
  have h := l2WholeLineFundamentalMatrix_add_int u z x 1
  simp only [Int.cast_one,_root_.zpow_one,coe_l2MonodromyUnit] at h
  rw [h,discriminantXiMatrix_mul,det_l2Monodromy,one_mul]

theorem continuous_l2WholeLineDiscriminantGradient (u : IntervalPairL2) (z : ℂ) :
    Continuous (l2WholeLineDiscriminantGradient u z) := by
  have hM := continuous_l2WholeLineFundamentalMatrix u z
  change Continuous (fun x => l2WholeLineDiscriminantGradient u z x)
  simp only [l2WholeLineDiscriminantGradient,discriminantGradientMatrix,discriminantGradientState]
  fun_prop

theorem ae_hasDerivAt_l2WholeLineDiscriminantGradient (u : IntervalPairL2) (z : ℂ) :
    ∀ᵐ x : ℝ, HasDerivAt (l2WholeLineDiscriminantGradient u z)
      (2*I*z*(l2WholeLineDiscriminantGradient u z x).1+
        l2WholeLineDiscriminantXi u z x*(l2WholeLinePotential u x).2,
       -2*I*z*(l2WholeLineDiscriminantGradient u z x).2-
        l2WholeLineDiscriminantXi u z x*(l2WholeLinePotential u x).1) x := by
  filter_upwards [ae_hasDerivAt_l2WholeLineSolution u z ![1,0],
    ae_hasDerivAt_l2WholeLineSolution u z ![0,1]] with x ha hb
  have h := hasDerivAt_discriminantGradientState (l2Monodromy u z) _ _ _ z x ha hb
  simpa only [← l2WholeLineDiscriminantGradient_eq_state,
    ← l2WholeLineDiscriminantXi_eq_state] using h

theorem ae_hasDerivAt_l2WholeLineDiscriminantXi (u : IntervalPairL2) (z : ℂ) :
    ∀ᵐ x : ℝ, HasDerivAt (l2WholeLineDiscriminantXi u z)
      (2*(l2WholeLinePotential u x).1*(l2WholeLineDiscriminantGradient u z x).1-
       2*(l2WholeLinePotential u x).2*(l2WholeLineDiscriminantGradient u z x).2) x := by
  filter_upwards [ae_hasDerivAt_l2WholeLineSolution u z ![1,0],
    ae_hasDerivAt_l2WholeLineSolution u z ![0,1]] with x ha hb
  have h := hasDerivAt_discriminantXiState (l2Monodromy u z) _ _ _ z x ha hb
  simpa only [← l2WholeLineDiscriminantGradient_eq_state,
    ← l2WholeLineDiscriminantXi_eq_state] using h

end NLS.ZakharovShabat
