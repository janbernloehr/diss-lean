import NLS.ComplexAnalysis.QuadraticRootPrimitive
import NLS.ComplexAnalysis.QuadraticPhaseEvenOdd

/-! Exact logarithmic derivatives of gap-times-phase factors on a
regular quadratic root sheet. The remainder equation has forcing g-I;
that I term cancels the algebraic prefactor's logarithmic derivative. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem hasDerivAt_quadratic_phase_plus (R H : ℂ → ℂ) (τ d c g z : ℂ)
    (hR : AnalyticAt ℂ R z) (hne : R z ≠ 0)
    (hsq : (fun w => R w^2) =ᶠ[𝓝 z] quadraticRootPolynomial τ d)
    (hH : AnalyticAt ℂ H z)
    (heq : quadraticRootPolynomial τ d z*deriv H z+(z-τ)*H z = g-I) :
    HasDerivAt (fun w => c*(w-τ-R w)*Complex.exp (I*R w*H w))
      ((I*g/R z)*(c*(z-τ-R z)*Complex.exp (I*R z*H z))) z := by
  have hrd := hasDerivAt_root_of_sq_eq_quadratic R τ d z hR hne hsq
  have hrh := hasDerivAt_root_mul_of_quadratic_equation R H τ d (g-I) z hR hne hsq hH heq
  have hexp : HasDerivAt (fun w => Complex.exp (I*R w*H w))
      (Complex.exp (I*R z*H z)*(I*((g-I)/R z))) z := by
    simpa only [mul_assoc] using (hrh.const_mul I).cexp
  have hd := ((((hasDerivAt_id z).sub_const τ).sub hrd).fun_mul hexp).const_mul c
  convert! hd using 1
  · funext w
    dsimp only [Pi.sub_apply,id_eq]
    ring
  · dsimp only [Pi.sub_apply,id_eq]
    have hI : I*(g-I) = I*g+1 := by linear_combination -I_sq
    rw [← mul_div_assoc,hI]
    field_simp [hne]
    ring

theorem hasDerivAt_quadratic_phase_minus (R H : ℂ → ℂ) (τ d c g z : ℂ)
    (hR : AnalyticAt ℂ R z) (hne : R z ≠ 0)
    (hsq : (fun w => R w^2) =ᶠ[𝓝 z] quadraticRootPolynomial τ d)
    (hH : AnalyticAt ℂ H z)
    (heq : quadraticRootPolynomial τ d z*deriv H z+(z-τ)*H z = g-I) :
    HasDerivAt (fun w => c*(w-τ+R w)*Complex.exp (-I*R w*H w))
      ((-I*g/R z)*(c*(z-τ+R z)*Complex.exp (-I*R z*H z))) z := by
  have hs : (fun w => (-R w)^2) =ᶠ[𝓝 z] quadraticRootPolynomial τ d := by simpa only [neg_sq] using hsq
  have h := hasDerivAt_quadratic_phase_plus (fun w => -R w) H τ d c g z hR.neg (neg_ne_zero.mpr hne) hs hH heq
  simpa only [sub_neg_eq_add,mul_neg,neg_mul,div_neg,neg_div] using h

theorem branch_system_of_two_sheet_derivatives (D A B S : ℂ → ℂ) (f z : ℂ)
    (hD : DifferentiableAt ℂ D z) (hA : DifferentiableAt ℂ A z)
    (hB : DifferentiableAt ℂ B z) (hS : DifferentiableAt ℂ S z) (hne : S z ≠ 0)
    (hsq : (fun w => S w^2) =ᶠ[𝓝 z] D)
    (hplus : HasDerivAt (fun w => A w+S w*B w) ((f/S z)*(A z+S z*B z)) z)
    (hminus : HasDerivAt (fun w => A w-S w*B w) ((-f/S z)*(A z-S z*B z)) z) :
    deriv A z = f*B z ∧ D z*deriv B z+(deriv D z/2)*B z = f*A z := by
  have hp := (hA.hasDerivAt.add (hS.hasDerivAt.fun_mul hB.hasDerivAt)).unique hplus
  have hm := (hA.hasDerivAt.sub (hS.hasDerivAt.fun_mul hB.hasDerivAt)).unique hminus
  have hd := ((hS.hasDerivAt.pow 2).congr_of_eventuallyEq hsq.symm).unique hD.hasDerivAt
  have hv : S z^2 = D z := hsq.eq_of_nhds
  simp only [Nat.cast_ofNat,show (2:ℕ)-1 = 1 from rfl,pow_one] at hd
  field_simp [hne] at hp hm
  constructor
  · apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) hne)
    linear_combination hp+hm
  · rw [← hv]
    linear_combination (hp-hm)/2-(B z/2)*hd

end NLS.ComplexAnalysis
