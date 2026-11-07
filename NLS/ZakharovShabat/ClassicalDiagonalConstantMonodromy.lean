import NLS.ZakharovShabat.ClassicalFundamentalSolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The actual monodromy at the smooth real constant potential (1,1) -/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

def classicalDiagonalOnePotential : Curve (ℂ × ℂ) := ⟨fun _ => (1,1),continuous_const⟩

theorem classicalDiagonalOne_first_column (t : Icc (0:ℝ) 1) :
    classicalSolution classicalDiagonalOnePotential 0 (1,0) t =
      ((Real.cosh t.val:ℂ),-I*(Real.sinh t.val:ℂ)) := by
  have h := classicalSolution_unique classicalDiagonalOnePotential 0 (1,0)
    (fun x : ℝ => ((Real.cosh x:ℂ),-I*(Real.sinh x:ℂ))) (by fun_prop) (by simp) (by
      intro x _
      have hc := (Real.hasDerivAt_cosh x.val).ofReal_comp
      have hs := (Real.hasDerivAt_sinh x.val).ofReal_comp
      have hd := hc.prodMk (hs.const_mul (-I))
      convert! hd using 1
      apply Prod.ext <;> simp only [classicalODECoefficient_apply,classicalDiagonalOnePotential,
        ContinuousMap.coe_mk,zero_mul,mul_zero,zero_add,add_zero] <;>
        ring_nf
      all_goals simp only [I_sq,neg_one_mul,neg_neg])
  exact (h t.property).symm

theorem classicalDiagonalOne_second_column (t : Icc (0:ℝ) 1) :
    classicalSolution classicalDiagonalOnePotential 0 (0,1) t =
      (I*(Real.sinh t.val:ℂ),(Real.cosh t.val:ℂ)) := by
  have h := classicalSolution_unique classicalDiagonalOnePotential 0 (0,1)
    (fun x : ℝ => (I*(Real.sinh x:ℂ),(Real.cosh x:ℂ))) (by fun_prop) (by simp) (by
      intro x _
      have hc := (Real.hasDerivAt_cosh x.val).ofReal_comp
      have hs := (Real.hasDerivAt_sinh x.val).ofReal_comp
      have hd := (hs.const_mul I).prodMk hc
      convert! hd using 1
      apply Prod.ext <;> simp only [classicalODECoefficient_apply,classicalDiagonalOnePotential,
        ContinuousMap.coe_mk,zero_mul,mul_zero,zero_add,add_zero] <;>
        ring_nf
      all_goals simp only [I_sq,neg_one_mul,neg_neg])
  exact (h t.property).symm

theorem classicalMonodromy_diagonalOne :
    classicalMonodromy classicalDiagonalOnePotential 0 =
      !![(Real.cosh 1:ℂ),I*(Real.sinh 1:ℂ);-I*(Real.sinh 1:ℂ),(Real.cosh 1:ℂ)] := by
  have h1 := classicalDiagonalOne_first_column ⟨1,by norm_num⟩
  have h2 := classicalDiagonalOne_second_column ⟨1,by norm_num⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [classicalMonodromy,classicalFundamentalMatrix,h1,h2]

end NLS.ZakharovShabat
