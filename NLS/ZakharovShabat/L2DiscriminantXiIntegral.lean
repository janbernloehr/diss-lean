import NLS.ZakharovShabat.L2DiscriminantSpatialEquation
import NLS.ZakharovShabat.L2WholeLinePeriodAbsoluteContinuity
import NLS.ZakharovShabat.L2GradientCurves

/-! # The scalar transport coefficient as an actual physical integral

Absolute continuity is established from the original Volterra solutions.
The a.e. transport equation then gives its exact normalized integral.
The physical convention here has R=diag(i,-i) and the unconjugated
Fréchet gradient, fixing the sign in the last formula.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

theorem absolutelyContinuousOnInterval_l2DiscriminantXi (u : IntervalPairL2) (z : ℂ) :
    AbsolutelyContinuousOnInterval (l2DiscriminantXi u z) 0 1 := by
  have ha := absolutelyContinuousOnInterval_l2SolutionCurve u z (1,0)
  have hb := absolutelyContinuousOnInterval_l2SolutionCurve u z (0,1)
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
  dsimp [l2DiscriminantXi,discriminantXiState]
  ring

theorem intervalIntegrable_l2DiscriminantXi_derivative (u : IntervalPairL2) (z : ℂ)
    (t : Icc (0:ℝ) 1) :
    IntervalIntegrable (fun x =>
      2*(intervalL2Representative u x).1*(l2DiscriminantGradient u z x).1-
      2*(intervalL2Representative u x).2*(l2DiscriminantGradient u z x).2) volume 0 t.val := by
  have h1 := (intervalIntegrable_intervalL2_mul u.fst
    (l2BoundedFirst (l2DiscriminantGradientCurve u z)) t).const_mul (2:ℂ)
  have h2 := (intervalIntegrable_intervalL2_mul u.snd
    (l2BoundedSecond (l2DiscriminantGradientCurve u z)) t).const_mul (2:ℂ)
  convert! h1.sub h2 using 1
  funext x
  simp only [l2BoundedFirst,l2BoundedSecond,ContinuousLinearMap.compLeftContinuousBounded_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',curveBoundedExtension_apply,
    extend_l2DiscriminantGradientCurve]
  dsimp [intervalL2Representative]
  ring

theorem l2DiscriminantXi_eq_integral (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2DiscriminantXi u z t = (l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1+
      ∫ x in (0:ℝ)..t.val,
        2*(intervalL2Representative u x).1*(l2DiscriminantGradient u z x).1-
        2*(intervalL2Representative u x).2*(l2DiscriminantGradient u z x).2 := by
  have hs : uIcc (0:ℝ) t.val ⊆ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le t.property.1,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl t.property.2
  have hd := ae_hasDerivAt_l2DiscriminantXi u z
  rw [ae_restrict_iff' measurableSet_Ioc] at hd
  have hglobal : ∀ᵐ x : ℝ, x ∈ uIcc (0:ℝ) t.val → HasDerivAt (l2DiscriminantXi u z)
      (2*(intervalL2Representative u x).1*(l2DiscriminantGradient u z x).1-
       2*(intervalL2Representative u x).2*(l2DiscriminantGradient u z x).2) x := by
    filter_upwards [hd,(show ∀ᵐ x : ℝ, x ≠ (0:ℝ) by simp [ae_iff])] with x hx hx0
    intro hxt
    have hx1 : x ∈ Icc (0:ℝ) 1 := by simpa using hs hxt
    exact hx ⟨lt_of_le_of_ne hx1.1 (Ne.symm hx0),hx1.2⟩
  have hi := integral_eq_sub_of_ac_of_ae_hasDerivAt
    ((absolutelyContinuousOnInterval_l2DiscriminantXi u z).mono hs)
    (intervalIntegrable_l2DiscriminantXi_derivative u z t) hglobal
  rw [l2DiscriminantXi_zero] at hi
  linear_combination -hi

/-- The exact R-convention formula, derived from the physical ODE and
actual gradient. It avoids any choice of generic Floquet eigenvectors. -/
theorem l2DiscriminantXi_eq_R_integral (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2DiscriminantXi u z t = (l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1-
      2*I*∫ x in (0:ℝ)..t.val,
        (I*(intervalL2Representative u x).1)*(l2DiscriminantGradient u z x).1+
        (-I*(intervalL2Representative u x).2)*(l2DiscriminantGradient u z x).2 := by
  rw [l2DiscriminantXi_eq_integral]
  have he : (fun x =>
      2*(intervalL2Representative u x).1*(l2DiscriminantGradient u z x).1-
      2*(intervalL2Representative u x).2*(l2DiscriminantGradient u z x).2) =
      (fun x => (-2*I)*
        ((I*(intervalL2Representative u x).1)*(l2DiscriminantGradient u z x).1+
         (-I*(intervalL2Representative u x).2)*(l2DiscriminantGradient u z x).2)) := by
    funext x
    ring_nf
    simp only [I_sq]
    ring
  rw [he,intervalIntegral.integral_const_mul]
  ring

end NLS.ZakharovShabat
