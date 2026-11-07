import NLS.ZakharovShabat.ClassicalRationalMonodromy
import NLS.ZakharovShabat.ClassicalDiscriminantXiIntegral
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # A concrete obstruction to the printed nonlocal plus sign

For the actual normalized ZS equation at zero spectral parameter, the scalar
coefficient of the spatial gradient equation has derivative 2-pi at the
left endpoint. The printed positive integral has derivative pi-2. Unique
one-sided differentiation on [0,1] proves they cannot agree on that period.
-/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

theorem classicalDiscriminantRPairing_rational_zero :
    classicalDiscriminantRPairing classicalRationalPotential 0 0 = I*(1-(Real.pi:ℂ)/2) := by
  have hp : extend classicalRationalPotential 0 = (-2*I,I) := by
    have h := extend_coe classicalRationalPotential ⟨0,by norm_num⟩
    simpa [classicalRationalPotential] using h
  rw [classicalDiscriminantRPairing,hp,classicalDiscriminantGradient_rational_zero]
  ring_nf
  simp only [I_pow_three]
  ring

theorem hasDerivAt_classicalDiscriminantXi_rational_zero :
    HasDerivAt (classicalDiscriminantXi classicalRationalPotential 0) (2-(Real.pi:ℂ)) 0 := by
  have h := hasDerivAt_classicalDiscriminantXi classicalRationalPotential 0 ⟨0,by norm_num⟩
  rw [classicalDiscriminantRPairing_rational_zero] at h
  convert! h using 1
  ring_nf
  simp only [I_sq]
  ring

theorem hasDerivAt_classicalPrintedDiscriminantXi_rational_zero :
    HasDerivAt (classicalPrintedDiscriminantXi classicalRationalPotential 0) ((Real.pi:ℂ)-2) 0 := by
  have h := hasDerivAt_classicalPrintedDiscriminantXi classicalRationalPotential 0 0
  rw [classicalDiscriminantRPairing_rational_zero] at h
  convert! h using 1
  ring_nf
  simp only [I_sq]
  ring

theorem printed_nonlocal_sign_not_eqOn :
    ¬ EqOn (classicalPrintedDiscriminantXi classicalRationalPotential 0)
      (classicalDiscriminantXi classicalRationalPotential 0) (Icc (0:ℝ) 1) := by
  intro he
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have hright := hasDerivAt_classicalPrintedDiscriminantXi_rational_zero.hasDerivWithinAt
    (s := Icc (0:ℝ) 1)
  have hactual := hasDerivAt_classicalDiscriminantXi_rational_zero.hasDerivWithinAt
    (s := Icc (0:ℝ) 1)
  have hconverted := hright.congr_of_mem (fun x hx => (he hx).symm) h0
  have hunique := uniqueDiffOn_Icc_zero_one 0 h0
  have hd := (hactual.derivWithin hunique).symm.trans (hconverted.derivWithin hunique)
  have hre := congrArg Complex.re hd
  norm_num at hre
  linarith [Real.pi_gt_three]

/-- The printed scalar coefficient cannot satisfy the printed spatial equation
for every point, even for this elementary continuous complex potential. -/
theorem printed_nonlocal_spatial_equation_false :
    ¬ (∀ x : Icc (0:ℝ) 1,
      HasDerivAt (classicalDiscriminantGradient classicalRationalPotential 0)
        (classicalPrintedDiscriminantXi classicalRationalPotential 0 x*(classicalRationalPotential x).2,
         -classicalPrintedDiscriminantXi classicalRationalPotential 0 x*(classicalRationalPotential x).1) x) := by
  intro h
  apply printed_nonlocal_sign_not_eqOn
  intro x hx
  let t : Icc (0:ℝ) 1 := ⟨x,hx⟩
  have he := (h t).unique (hasDerivAt_classicalDiscriminantGradient_spatial classicalRationalPotential 0 t)
  have hs := congrArg Prod.snd he
  have hc : -classicalPrintedDiscriminantXi classicalRationalPotential 0 x*(-2*I) =
      -classicalDiscriminantXi classicalRationalPotential 0 x*(-2*I) := by
    simpa [classicalRationalPotential,t] using hs
  exact neg_injective (mul_right_cancel₀ (mul_ne_zero (by norm_num) I_ne_zero) hc)

/-- The obstruction persists for the weak, almost-everywhere reading on
original rough periodic L2 potentials; it is not an endpoint-only issue. -/
theorem printed_nonlocal_spatial_equation_false_ae :
    ¬ (∀ᵐ x ∂MeasureTheory.volume.restrict (Ioc (0:ℝ) 1),
      HasDerivAt (classicalDiscriminantGradient classicalRationalPotential 0)
        (classicalPrintedDiscriminantXi classicalRationalPotential 0 x*(extend classicalRationalPotential x).2,
         -classicalPrintedDiscriminantXi classicalRationalPotential 0 x*(extend classicalRationalPotential x).1) x) := by
  intro h
  have he : classicalPrintedDiscriminantXi classicalRationalPotential 0 =ᵐ[
      MeasureTheory.volume.restrict (Ioc (0:ℝ) 1)] classicalDiscriminantXi classicalRationalPotential 0 := by
    filter_upwards [h,MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx hmem
    let t : Icc (0:ℝ) 1 := ⟨x,hmem.1.le,hmem.2⟩
    have ha := hasDerivAt_classicalDiscriminantGradient_spatial classicalRationalPotential 0 t
    have hs := congrArg Prod.snd (hx.unique ha)
    have hp : (extend classicalRationalPotential x).1 = -2*I := by
      simp [NLS.LinearVolterra.extend,classicalRationalPotential]
    rw [hp] at hs
    have hc : -classicalPrintedDiscriminantXi classicalRationalPotential 0 x*(-2*I) =
        -classicalDiscriminantXi classicalRationalPotential 0 x*(-2*I) := by
      simpa [classicalRationalPotential,t] using hs
    exact neg_injective (mul_right_cancel₀ (mul_ne_zero (by norm_num) I_ne_zero) hc)
  rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc] at he
  have hp : Continuous (classicalPrintedDiscriminantXi classicalRationalPotential 0) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (hasDerivAt_classicalPrintedDiscriminantXi classicalRationalPotential 0 x).continuousAt)
  exact printed_nonlocal_sign_not_eqOn (MeasureTheory.Measure.eqOn_Icc_of_ae_eq MeasureTheory.volume
    (by norm_num : (0:ℝ) ≠ 1) he hp.continuousOn
    (continuous_classicalDiscriminantXi classicalRationalPotential 0).continuousOn)

end NLS.ZakharovShabat
