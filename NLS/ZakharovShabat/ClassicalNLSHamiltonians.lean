import NLS.ZakharovShabat.NLSRiccatiHierarchy
import NLS.ZakharovShabat.ClassicalDiscriminantMassAsymptotics
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # The physical NLS Hamiltonians with the dissertation's normalization

Appendix H defines the positive-index Hamiltonians by integrating the
Riccati densities over one period. The first three are mass, momentum,
and NLS energy. The zero-index value is set to zero.
-/
noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The physical hierarchy from Appendix H, indexed as `H_1,H_2,...`. -/
def classicalNLSHamiltonian (a b : ℝ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n+1 => (-I)^(n+2) * ∫ x in (0 : ℝ)..1, a x*nlsRiccatiDensity a b n x

@[simp] theorem classicalNLSHamiltonian_one (a b : ℝ → ℂ) :
    classicalNLSHamiltonian a b 1 = ∫ x in (0 : ℝ)..1, a x*b x := by
  simp only [classicalNLSHamiltonian,nlsRiccatiDensity_zero,Pi.neg_apply,mul_neg,intervalIntegral.integral_neg]
  norm_num [I_sq]

/-- The hierarchy's first Hamiltonian agrees with the already-calibrated
physical mass of the actual continuous potential. -/
theorem classicalNLSHamiltonian_one_eq_mass (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) :
    classicalNLSHamiltonian (fun x => (NLS.LinearVolterra.extend φ x).1)
      (fun x => (NLS.LinearVolterra.extend φ x).2) 1 = classicalPhysicalMass φ :=
  classicalNLSHamiltonian_one _ _

theorem classicalNLSHamiltonian_two_unsymmetrized (a b : ℝ → ℂ) :
    classicalNLSHamiltonian a b 2 = -I * ∫ x in (0 : ℝ)..1, a x*deriv b x := by
  simp only [classicalNLSHamiltonian,nlsRiccatiDensity_one,Pi.neg_apply,mul_neg,intervalIntegral.integral_neg]
  norm_num [pow_succ,I_sq]

/-- Spatial differentiation preserves periodicity, without regularity
assumptions beyond those implicit in the total derivative. -/
theorem periodic_deriv_of_periodic (f : ℝ → ℂ) (T : ℝ) (hf : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  have he : (fun y => f (y+T)) = f := funext hf
  have hd := deriv_comp_add_const f T x
  rw [he] at hd
  exact hd.symm

/-- Every recursively generated density retains the source period. -/
theorem periodic_nlsRiccatiDensity (a b : ℝ → ℂ) (T : ℝ)
    (ha : Function.Periodic a T) (hb : Function.Periodic b T) (n : ℕ) :
    Function.Periodic (nlsRiccatiDensity a b n) T := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [nlsRiccatiDensity_zero]
      intro x
      change -b (x+T) = -b x
      rw [hb x]
    · rw [nlsRiccatiDensity_one]
      intro x
      change -deriv b (x+T) = -deriv b x
      rw [periodic_deriv_of_periodic b T hb x]
    · rw [nlsRiccatiDensity_succ_succ]
      apply (periodic_deriv_of_periodic _ T (ih (n+1) (by omega))).add
      apply ha.mul
      intro x
      simp only [Finset.sum_apply,Pi.mul_apply]
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.mem_antidiagonal.mp hij
      rw [ih ij.1 (by omega) x,ih ij.2 (by omega) x]

/-- Smooth periodic potentials define genuine integrable Hamiltonian
densities at every order. -/
theorem intervalIntegrable_nlsRiccatiDensity (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (n : ℕ) :
    IntervalIntegrable (fun x => a x*nlsRiccatiDensity a b n x) volume 0 1 :=
  (ha.continuous.mul (contDiff_nlsRiccatiDensity a b ha hb n).continuous).intervalIntegrable 0 1

private theorem integral_mul_deriv_periodic (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) :
    (∫ x in (0 : ℝ)..1, a x*deriv b x) = -(∫ x in (0 : ℝ)..1, deriv a x*b x) := by
  have h := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt ha.continuous.continuousOn hb.continuous.continuousOn
    (fun x _ => ((contDiff_infty_iff_deriv.mp ha).1 x).hasDerivAt)
    (fun x _ => ((contDiff_infty_iff_deriv.mp hb).1 x).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp ha).2.continuous.intervalIntegrable 0 1)
    ((contDiff_infty_iff_deriv.mp hb).2.continuous.intervalIntegrable 0 1)
  have henda : a 1 = a 0 := by simpa using hpa 0
  have hendb : b 1 = b 0 := by simpa using hpb 0
  simpa only [henda,hendb,sub_self,zero_sub] using h

/-- The second Hamiltonian is exactly the symmetrized momentum in the
normalization printed in the dissertation. -/
theorem classicalNLSHamiltonian_two (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) :
    classicalNLSHamiltonian a b 2 = I/2 *
      ∫ x in (0 : ℝ)..1, deriv a x*b x-a x*deriv b x := by
  have hai : IntervalIntegrable (fun x => deriv a x*b x) volume 0 1 := ((contDiff_infty_iff_deriv.mp ha).2.continuous.mul hb.continuous).intervalIntegrable (μ := volume) (a := 0) (b := 1)
  have hbi : IntervalIntegrable (fun x => a x*deriv b x) volume 0 1 := (ha.continuous.mul (contDiff_infty_iff_deriv.mp hb).2.continuous).intervalIntegrable (μ := volume) (a := 0) (b := 1)
  rw [classicalNLSHamiltonian_two_unsymmetrized,intervalIntegral.integral_sub hai hbi,integral_mul_deriv_periodic a b ha hb hpa hpb]
  ring

/-- The third Hamiltonian is exactly the usual NLS energy. -/
theorem classicalNLSHamiltonian_three (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) :
    classicalNLSHamiltonian a b 3 =
      ∫ x in (0 : ℝ)..1, deriv a x*deriv b x+(a x)^2*(b x)^2 := by
  have hdb := (contDiff_infty_iff_deriv.mp hb).2
  have hparts := integral_mul_deriv_periodic a (deriv b) ha hdb hpa (periodic_deriv_of_periodic b 1 hpb)
  have hi : IntervalIntegrable (fun x => a x*deriv (deriv b) x) volume 0 1 := (ha.continuous.mul (contDiff_infty_iff_deriv.mp hdb).2.continuous).intervalIntegrable (μ := volume) (a := 0) (b := 1)
  have hq : IntervalIntegrable (fun x => a x^2*b x^2) volume 0 1 := ((ha.continuous.pow 2).mul (hb.continuous.pow 2)).intervalIntegrable (μ := volume) (a := 0) (b := 1)
  have hk : IntervalIntegrable (fun x => deriv a x*deriv b x) volume 0 1 := ((contDiff_infty_iff_deriv.mp ha).2.continuous.mul hdb.continuous).intervalIntegrable (μ := volume) (a := 0) (b := 1)
  simp only [classicalNLSHamiltonian,nlsRiccatiDensity_two,Pi.add_apply,Pi.neg_apply,Pi.mul_apply,Pi.pow_apply]
  norm_num [show (-I)^4 = (1 : ℂ) by norm_num [pow_succ,I_sq]]
  have he (x : ℝ) : a x*(-deriv (deriv b) x+a x*b x^2) = -(a x*deriv (deriv b) x)+a x^2*b x^2 := by ring
  simp_rw [he]
  have hni : IntervalIntegrable (fun x => -(a x*deriv (deriv b) x)) volume 0 1 := by
    simpa only [Pi.neg_apply] using! hi.neg
  rw [intervalIntegral.integral_add hni hq,intervalIntegral.integral_neg,hparts,neg_neg,intervalIntegral.integral_add hk hq]

/-- Each integrated Riccati term has exactly the Hamiltonian normalization
`i*H_k/(2*z)^k` used in Lemma 19.2. This is an algebraic identity and
makes no assertion that the formal expansion converges to the primitive. -/
theorem classicalNLSHamiltonian_riccati_coefficient (a b : ℝ → ℂ) (n : ℕ) (z : ℂ) :
    (∫ x in (0 : ℝ)..1, a x*nlsRiccatiDensity a b n x) / (2*I*z)^(n+1) =
      I*classicalNLSHamiltonian a b (n+1)/(2*z)^(n+1) := by
  have hI : I⁻¹ = -I := by norm_num
  have hc : I*(-I)^(n+2) = (-I)^(n+1) := by
    rw [show n+2 = (n+1)+1 by omega,pow_succ]
    calc
      I*((-I)^(n+1)*(-I)) = (I*(-I))*(-I)^(n+1) := by ring
      _ = (-I)^(n+1) := by simp [I_mul_I]
  simp only [classicalNLSHamiltonian]
  rw [← mul_assoc,hc]
  rw [show 2*I*z = (2*z)*I by ring,mul_pow,div_mul_eq_div_mul_one_div,one_div,
    ← inv_pow,hI]
  ring

end NLS.ZakharovShabat
