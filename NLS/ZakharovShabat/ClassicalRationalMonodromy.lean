import NLS.ZakharovShabat.ClassicalDiscriminantGradient
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! # An explicit nonconstant physical ZS potential at zero frequency

The smooth unit-interval potential (-2i, i/(1+x²)) has elementary normalized
columns. It supplies a concrete sign test using the actual ODE, monodromy
and unconjugated Fréchet discriminant gradient.
-/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

private theorem rationalDenominator_ne_zero (x : ℝ) : (1:ℂ)+(x:ℂ)^2 ≠ 0 := by
  exact_mod_cast (show (1:ℝ)+x^2 ≠ 0 by positivity)

def classicalRationalPotential : Curve (ℂ × ℂ) :=
  ⟨fun t => (-2*I,I/(1+(t.val:ℂ)^2)),by
    apply continuous_const.prodMk
    exact continuous_const.div (by fun_prop) (fun t => rationalDenominator_ne_zero t)⟩

theorem classicalRational_first_column (t : Icc (0:ℝ) 1) :
    classicalSolution classicalRationalPotential 0 (1,0) t = (1+(t.val:ℂ)^2,(t.val:ℂ)) := by
  have h := classicalSolution_unique classicalRationalPotential 0 (1,0)
    (fun x : ℝ => (1+(x:ℂ)^2,(x:ℂ))) (by fun_prop) (by norm_num) (by
      intro x _
      have hx := Complex.ofRealCLM.hasDerivAt (x := x.val)
      have hd := ((hx.pow 2).const_add 1).prodMk hx
      convert! hd using 1
      apply Prod.ext <;> simp only [classicalODECoefficient_apply,classicalRationalPotential,
        ContinuousMap.coe_mk,zero_mul,mul_zero,zero_add,add_zero] <;> dsimp <;>
        field_simp [rationalDenominator_ne_zero x.val] <;> ring_nf <;> simp only [I_sq] <;> ring)
  exact (h t.property).symm

theorem classicalRational_second_column (t : Icc (0:ℝ) 1) :
    classicalSolution classicalRationalPotential 0 (0,1) t =
      ((t.val:ℂ)+(1+(t.val:ℂ)^2)*(Real.arctan t.val:ℂ),
       1+(t.val:ℂ)*(Real.arctan t.val:ℂ)) := by
  have h := classicalSolution_unique classicalRationalPotential 0 (0,1)
    (fun x : ℝ => ((x:ℂ)+(1+(x:ℂ)^2)*(Real.arctan x:ℂ),
      1+(x:ℂ)*(Real.arctan x:ℂ))) (by fun_prop) (by norm_num) (by
      intro x _
      have hx := Complex.ofRealCLM.hasDerivAt (x := x.val)
      have hat : HasDerivAt (fun r : ℝ => (Real.arctan r:ℂ)) (1/(1+(x.val:ℂ)^2)) x.val := by
        exact_mod_cast (Real.hasDerivAt_arctan x.val).ofReal_comp
      have hd := (hx.add (((hx.pow 2).const_add 1).mul hat)).prodMk
        ((hx.mul hat).const_add 1)
      convert! hd using 1
      apply Prod.ext <;> simp only [classicalODECoefficient_apply,classicalRationalPotential,
        ContinuousMap.coe_mk,zero_mul,mul_zero,zero_add,add_zero] <;> dsimp <;>
        field_simp [rationalDenominator_ne_zero x.val] <;> ring_nf <;> simp only [I_sq] <;> ring)
  exact (h t.property).symm

theorem classicalMonodromy_rational :
    classicalMonodromy classicalRationalPotential 0 =
      !![2,1+(Real.pi:ℂ)/2;1,1+(Real.pi:ℂ)/4] := by
  have h1 := classicalRational_first_column ⟨1,by norm_num⟩
  have h2 := classicalRational_second_column ⟨1,by norm_num⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [classicalMonodromy,classicalFundamentalMatrix,h1,h2,Real.arctan_one] <;> ring

theorem classicalDiscriminantGradient_rational_zero :
    classicalDiscriminantGradient classicalRationalPotential 0 0 =
      (I,-I*(1+(Real.pi:ℂ)/2)) := by
  simp [classicalDiscriminantGradient,classicalMonodromy_rational]
  ring

end NLS.ZakharovShabat
