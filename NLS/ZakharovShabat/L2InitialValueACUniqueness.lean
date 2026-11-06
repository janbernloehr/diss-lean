import NLS.ZakharovShabat.L2VolterraInverse
import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity

/-! Uniqueness for actual physical L2 ODE solutions in the absolutely
continuous class. The integral equation is proved from the weak equation. -/
noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Every absolutely continuous physical solution is the actual L2 IVP
solution with its own initial value. An a.e. ODE alone is not assumed sufficient. -/
theorem l2SolutionCurve_unique_of_ac (u : IntervalPairL2) (z : ℂ)
    (w : Curve (ℂ × ℂ))
    (hw : AbsolutelyContinuousOnInterval (extend w) 0 1)
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt (extend w)
      (classicalODECoefficient (intervalL2Representative u x) z (extend w x)) x) :
    w = l2SolutionCurve u z (w ⟨0,by constructor <;> norm_num⟩) := by
  apply l2SolutionCurve_unique_integral
  intro t
  have hs : uIcc (0:ℝ) t.val ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le t.property.1]
    exact Icc_subset_Icc le_rfl t.property.2
  have hglobal : ∀ᵐ x : ℝ, x ∈ uIcc (0:ℝ) t.val → HasDerivAt (extend w)
      (classicalODECoefficient (intervalL2Representative u x) z (extend w x)) x := by
    rw [ae_restrict_iff' measurableSet_Ioc] at hd
    filter_upwards [hd,(show ∀ᵐ x : ℝ, x ≠ (0:ℝ) by simp [ae_iff])] with x hx hx0
    intro hxt
    have hx1 := hs hxt
    exact hx ⟨lt_of_le_of_ne hx1.1 (Ne.symm hx0),hx1.2⟩
  have hi := integral_eq_sub_of_ac_of_ae_hasDerivAt
    (hw.mono (by simpa using hs)) (intervalIntegrable_l2ODECoefficient u z w t) hglobal
  rw [l2ODEIntegral,hi,extend_coe w t,extend_coe w ⟨0,by constructor <;> norm_num⟩]
  abel

end NLS.ZakharovShabat
