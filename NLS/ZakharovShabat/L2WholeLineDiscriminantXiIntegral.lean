import NLS.ZakharovShabat.L2WholeLineDiscriminantGradient

/-! # The normalized scalar transport integral at every real spatial point

Actual whole-line Volterra solutions give absolute continuity across all
integer seams. Their scalar transport coefficient is periodic and satisfies
one integral formula at positive and negative times, for arbitrary L2 input.
-/
noncomputable section
open Set Complex Matrix MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

theorem absolutelyContinuousOnInterval_l2WholeLineDiscriminantXi
    (u : IntervalPairL2) (z : ℂ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (l2WholeLineDiscriminantXi u z) a b := by
  have ha := absolutelyContinuousOnInterval_l2WholeLineSolution u z ![1,0] a b
  have hb := absolutelyContinuousOnInterval_l2WholeLineSolution u z ![0,1] a b
  have ha1 := absolutelyContinuousOnInterval_clm ha (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have ha2 := absolutelyContinuousOnInterval_clm ha (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hb1 := absolutelyContinuousOnInterval_clm hb (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hb2 := absolutelyContinuousOnInterval_clm hb (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have h := ((((ha1.smul hb2).add (ha2.smul hb1)).const_smul
    ((l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1)).sub
    ((ha1.smul ha2).const_smul (2*(l2Monodromy u z) 0 1))).add
    ((hb1.smul hb2).const_smul (2*(l2Monodromy u z) 1 0))
  convert! h using 1
  funext x
  rw [l2WholeLineDiscriminantXi_eq_state]
  dsimp [discriminantXiState]
  ring

theorem intervalIntegrable_l2WholeLineDiscriminantXi_derivative
    (u : IntervalPairL2) (z : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun x =>
      2*(l2WholeLinePotential u x).1*(l2WholeLineDiscriminantGradient u z x).1-
      2*(l2WholeLinePotential u x).2*(l2WholeLineDiscriminantGradient u z x).2) volume a b := by
  have hg := continuous_l2WholeLineDiscriminantGradient u z
  have h1 := (LocallyIntegrable.mul_continuous hg.fst (locallyIntegrable_l2WholeLinePotential_fst u)).smul (2:ℂ)
  have h2 := (LocallyIntegrable.mul_continuous hg.snd (locallyIntegrable_l2WholeLinePotential_snd u)).smul (2:ℂ)
  have h := (h1.sub h2).integrableOn_isCompact (isCompact_uIcc (a := a) (b := b))
  apply intervalIntegrable_iff.mpr
  convert! h.mono_set uIoc_subset_uIcc using 1
  funext x
  dsimp
  ring

theorem l2WholeLineDiscriminantXi_zero (u : IntervalPairL2) (z : ℂ) :
    l2WholeLineDiscriminantXi u z 0 = (l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1 := by
  rw [l2WholeLineDiscriminantXi_eq_state,l2WholeLineSolution_zero,l2WholeLineSolution_zero]
  simp [discriminantXiState]

theorem l2WholeLineDiscriminantXi_eq_integral (u : IntervalPairL2) (z : ℂ) (t : ℝ) :
    l2WholeLineDiscriminantXi u z t = (l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1+
      ∫ x in (0:ℝ)..t,
        2*(l2WholeLinePotential u x).1*(l2WholeLineDiscriminantGradient u z x).1-
        2*(l2WholeLinePotential u x).2*(l2WholeLineDiscriminantGradient u z x).2 := by
  have hd : ∀ᵐ x : ℝ, x ∈ uIcc (0:ℝ) t → HasDerivAt (l2WholeLineDiscriminantXi u z)
      (2*(l2WholeLinePotential u x).1*(l2WholeLineDiscriminantGradient u z x).1-
       2*(l2WholeLinePotential u x).2*(l2WholeLineDiscriminantGradient u z x).2) x := by
    filter_upwards [ae_hasDerivAt_l2WholeLineDiscriminantXi u z] with x hx _
    exact hx
  have hi := integral_eq_sub_of_ac_of_ae_hasDerivAt
    (absolutelyContinuousOnInterval_l2WholeLineDiscriminantXi u z 0 t)
    (intervalIntegrable_l2WholeLineDiscriminantXi_derivative u z 0 t) hd
  rw [l2WholeLineDiscriminantXi_zero] at hi
  linear_combination -hi

theorem l2WholeLineDiscriminantXi_eq_R_integral (u : IntervalPairL2) (z : ℂ) (t : ℝ) :
    l2WholeLineDiscriminantXi u z t = (l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1-
      2*I*∫ x in (0:ℝ)..t,
        (I*(l2WholeLinePotential u x).1)*(l2WholeLineDiscriminantGradient u z x).1+
        (-I*(l2WholeLinePotential u x).2)*(l2WholeLineDiscriminantGradient u z x).2 := by
  rw [l2WholeLineDiscriminantXi_eq_integral]
  have he : (fun x =>
      2*(l2WholeLinePotential u x).1*(l2WholeLineDiscriminantGradient u z x).1-
      2*(l2WholeLinePotential u x).2*(l2WholeLineDiscriminantGradient u z x).2) =
      (fun x => (-2*I)*
        ((I*(l2WholeLinePotential u x).1)*(l2WholeLineDiscriminantGradient u z x).1+
         (-I*(l2WholeLinePotential u x).2)*(l2WholeLineDiscriminantGradient u z x).2)) := by
    funext x
    ring_nf
    simp only [I_sq]
    ring
  rw [he,intervalIntegral.integral_const_mul]
  ring

end NLS.ZakharovShabat
