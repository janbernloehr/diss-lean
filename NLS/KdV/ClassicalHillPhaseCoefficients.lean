import NLS.KdV.ClassicalTraceAsymptotics
import NLS.KdV.ClassicalDiscriminant
import NLS.ZakharovShabat.NLSHamiltonianPrimitiveCoefficients

/-! # Physical coefficients of any actual normalized analytic Hill phase -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

theorem iteratedDeriv_classicalHill_phase
    (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0 = 0)
    (R : ℝ) (he : ∀ z : ℂ, R < ‖z‖ →
      2*cosh (-I*z+B z⁻¹) = classicalHillDiscriminant (scalarPotentialCurve q hq.continuous) (z^2))
    (k : ℕ) :
    iteratedDeriv (k+1) B 0 = ((k+1).factorial : ℂ)*
      (I*classicalNLSHamiltonian (fun _ => -1) (-q) (k+1)/2^(k+1)) := by
  apply iteratedDeriv_nlsHamiltonian_of_discriminant (fun _ => -1) (-q)
    contDiff_const hq.neg (fun _ => rfl) (fun x => congrArg Neg.neg (hp x)) B hB hB0
  filter_upwards [eventually_gt_atTop (max R 0)] with r hr
  have hn : R < ‖(r : ℂ)‖ := by
    rw [norm_real,Real.norm_eq_abs,abs_of_pos ((le_max_right _ _).trans_lt hr)]
    exact (le_max_left _ _).trans_lt hr
  simpa only [classicalHillDiscriminant_sq,constantUpperPotential_scalarPotentialCurve] using he r hn

/-- The cubic and fifth coefficients are calculated from the physical
quadratic invariant and KdV energy integrals, with their original constants. -/
theorem classicalHill_phase_first_five
    (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (hmean : (∫ x in (0 : ℝ)..1, q x) = 0)
    (B : ℂ → ℂ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0 = 0)
    (R : ℝ) (he : ∀ z : ℂ, R < ‖z‖ →
      2*cosh (-I*z+B z⁻¹) = classicalHillDiscriminant (scalarPotentialCurve q hq.continuous) (z^2)) :
    iteratedDeriv 1 B 0 = 0 ∧ iteratedDeriv 2 B 0 = 0 ∧
      iteratedDeriv 3 B 0 = 3*I*classicalQuadraticInvariant q/2 ∧
      iteratedDeriv 4 B 0 = 0 ∧ iteratedDeriv 5 B 0 = 15*I*classicalHamiltonian q/2 := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := classicalNLSHamiltonian_const_upper_first_five q hq hp hmean
  have hc := iteratedDeriv_classicalHill_phase q hq hp B hB hB0 R he
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [h1,mul_zero,zero_div] using hc 0
  · simpa only [h2,mul_zero,zero_div] using hc 1
  · rw [hc 2,h3]
    norm_num [Nat.factorial]
    ring
  · simpa only [h4,mul_zero,zero_div] using hc 3
  · rw [hc 4,h5]
    norm_num [Nat.factorial]
    ring

end NLS.KdV
