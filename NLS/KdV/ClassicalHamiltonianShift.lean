import NLS.KdV.ClassicalHamiltonian

/-! The exact constant-energy translation of the physical KdV Hamiltonian.
The physical unit period fixes the cubic constant without a length factor. -/
noncomputable section
open Complex MeasureTheory
open scoped ContDiff
namespace NLS.KdV

theorem classicalKdVHamiltonian_sub_const (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (c : ℂ) :
    classicalKdVHamiltonian (fun x => q x-c)=classicalKdVHamiltonian q-
      3*c*(∫ x in (0:ℝ)..1, (q x)^2)+3*c^2*(∫ x in (0:ℝ)..1, q x)-c^3 := by
  have hd := (contDiff_infty_iff_deriv.mp hq).2.continuous
  let K : ℝ → ℂ := fun x => (1/2:ℂ)*(deriv q x)^2+(q x)^3
  have hiK : IntervalIntegrable K volume 0 1 :=
    ((continuous_const.mul (hd.pow 2)).add (hq.continuous.pow 3)).intervalIntegrable 0 1
  have hiA : IntervalIntegrable (fun x => (3*c)*(q x)^2) volume 0 1 :=
    (continuous_const.mul (hq.continuous.pow 2)).intervalIntegrable 0 1
  have hiB : IntervalIntegrable (fun x => (3*c^2)*q x) volume 0 1 :=
    (continuous_const.mul hq.continuous).intervalIntegrable 0 1
  have hiC : IntervalIntegrable (fun _ : ℝ => c^3) volume 0 1 := intervalIntegrable_const
  calc
    _ = ∫ x in (0:ℝ)..1, K x-(3*c)*(q x)^2+(3*c^2)*q x-c^3 := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [K]
      rw [deriv_sub_const]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub ((hiK.sub hiA).add hiB) hiC,
        intervalIntegral.integral_add (hiK.sub hiA) hiB,intervalIntegral.integral_sub hiK hiA,
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
      simp only [sub_zero,one_smul]
      rfl

theorem classicalKdVHamiltonian_sub_mean (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (c : ℂ)
    (hc : (∫ x in (0:ℝ)..1, q x)=c) :
    classicalKdVHamiltonian (fun x => q x-c)=classicalKdVHamiltonian q-
      3*c*(∫ x in (0:ℝ)..1, (q x)^2)+2*c^3 := by
  rw [classicalKdVHamiltonian_sub_const q hq c,hc]
  ring

end NLS.KdV
