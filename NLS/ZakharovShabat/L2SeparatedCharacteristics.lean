import NLS.ZakharovShabat.L2Discriminant
import NLS.ZakharovShabat.L2FundamentalInitialValue
import NLS.ZakharovShabat.ClassicalSeparatedCharacteristics

/-! # The actual L2 separated characteristics and anti-discriminant

Use the original monodromy entries, the source sine normalization, and
both original separated endpoint signs for every physical L2 potential.
-/
noncomputable section
open Set Complex
open NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The source-normalized physical L2 separated characteristic. -/
def l2SeparatedCharacteristic (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) : ℂ :=
  ((l2Monodromy u z) 1 1-(l2Monodromy u z) 0 0+
    extensionSign b*((l2Monodromy u z) 1 0-(l2Monodromy u z) 0 1))/(2*I)

/-- The physical L2 anti-discriminant uses the established off-diagonal sum. -/
def l2AntiDiscriminant (u : IntervalPairL2) (z : ℂ) : ℂ :=
  (l2Monodromy u z) 0 1+(l2Monodromy u z) 1 0

theorem l2SeparatedCharacteristic_of_continuous (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    l2SeparatedCharacteristic b (continuousPotentialL2Class Φ) z = classicalSeparatedCharacteristic b Φ z := by
  simp only [l2SeparatedCharacteristic,l2Monodromy_of_continuous,classicalSeparatedCharacteristic]

theorem l2AntiDiscriminant_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    l2AntiDiscriminant (continuousPotentialL2Class Φ) z = classicalAntiDiscriminant Φ z := by
  simp only [l2AntiDiscriminant,l2Monodromy_of_continuous,classicalAntiDiscriminant]

/-- Joint frequency/potential analyticity on the full physical L2 space. -/
theorem analyticOnNhd_l2SeparatedCharacteristic_joint (b : BoundaryCondition) :
    AnalyticOnNhd ℂ (fun q : ℂ × IntervalPairL2 => l2SeparatedCharacteristic b q.2 q.1) univ := by
  intro q _
  have h := analyticOnNhd_l2Monodromy_joint q (mem_univ _)
  have hm (i j : Fin 2) := analyticAt_pi_iff.mp (analyticAt_pi_iff.mp h i) j
  exact (((hm 1 1).sub (hm 0 0)).add
    (analyticAt_const.mul ((hm 1 0).sub (hm 0 1)))).div
      analyticAt_const (mul_ne_zero (by norm_num) I_ne_zero)

theorem analyticOnNhd_l2AntiDiscriminant_joint :
    AnalyticOnNhd ℂ (fun q : ℂ × IntervalPairL2 => l2AntiDiscriminant q.2 q.1) univ := by
  intro q _
  have h := analyticOnNhd_l2Monodromy_joint q (mem_univ _)
  exact (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp h 0) 1).add
    (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp h 1) 0)

/-- The literal zero condition is the original separated endpoint equation for the actual L2 solution. -/
theorem l2SeparatedCharacteristic_eq_zero_iff (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    l2SeparatedCharacteristic b u z = 0 ↔
      (l2SolutionCurve u z (1,extensionSign b) ⟨1,by constructor <;> norm_num⟩).1 =
        extensionSign b*(l2SolutionCurve u z (1,extensionSign b) ⟨1,by constructor <;> norm_num⟩).2 := by
  rw [l2SeparatedCharacteristic,div_eq_zero_iff]
  simp only [mul_eq_zero,OfNat.ofNat_ne_zero,I_ne_zero,or_self,or_false]
  rw [l2SolutionCurve_linearCombination]
  simp only [l2Monodromy,l2FundamentalMatrix,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  cases b <;> simp only [extensionSign,one_mul,neg_one_mul] <;> constructor <;> intro h <;> linear_combination -h

@[simp] theorem l2SeparatedCharacteristic_zero (b : BoundaryCondition) (z : ℂ) :
    l2SeparatedCharacteristic b 0 z = sin z := by
  rw [← continuousPotentialL2Class_zero,l2SeparatedCharacteristic_of_continuous]
  exact classicalSeparatedCharacteristic_free b z

@[simp] theorem l2AntiDiscriminant_zero (z : ℂ) : l2AntiDiscriminant 0 z = 0 := by
  rw [← continuousPotentialL2Class_zero,l2AntiDiscriminant_of_continuous]
  exact classicalAntiDiscriminant_free z

/-- The determinant-one identity retains the exact signs and normalization for all physical L2 inputs. -/
theorem l2Discriminant_sq_sub_four (u : IntervalPairL2) (z : ℂ) :
    (l2Discriminant u z)^2-4 = (l2AntiDiscriminant u z)^2-
      4*l2SeparatedCharacteristic .dirichlet u z*l2SeparatedCharacteristic .neumann u z := by
  have hd := det_l2Monodromy u z
  simp only [Matrix.det_fin_two] at hd
  simp only [l2Discriminant,Matrix.trace_fin_two,l2AntiDiscriminant,l2SeparatedCharacteristic,
    extensionSign,one_mul,neg_one_mul]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,Complex.inv_I]
  linear_combination (norm := (ring_nf; simp [I_sq])) 4 * hd

end NLS.ZakharovShabat
