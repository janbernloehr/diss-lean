import NLS.MKdV.MiuraOppositeAngularCoordinateDescent
import NLS.ComplexAnalysis.ContinuousBoundedAngularProduct

/-! # Full unit-phase products on the exact selected open-angle locus

An independent unit phase is required to be continuous only where its
selected action is open. No angular extension across that closed action
is assumed. The amplitude-weighted product extends continuously by zero;
complete physical flows and the infinite action-fiber argument prove
its global factorization. Dividing by the action-dependent amplitude
recovers the product of full unit phases, rather than their squares.
The existence and Gardner identity of the independent phase remain
separate mathematical obligations.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraNativeNLSUnitPhase (s m : ℕ) (a : MiuraRealSobolevSource s) : ℂ :=
  miuraNativeNLSAngularCoordinate s m a/(‖miuraNativeNLSAngularCoordinate s m a‖ : ℂ)

theorem norm_miuraNativeNLSAngularCoordinate_actionFlow (s m : ℕ) (hm : 1 ≤ m)
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖miuraNativeNLSAngularCoordinate s m (miuraNativeRealActionFlow s a n t)‖ =
      ‖miuraNativeNLSAngularCoordinate s m a‖ := by
  rw [miuraNativeNLSAngularCoordinate_actionFlow s m hm a n hn t,norm_mul]
  by_cases hmn : m = n
  · rw [if_pos hmn,mul_comm I (t : ℂ),Complex.norm_exp_ofReal_mul_I,one_mul]
  · rw [if_neg hmn,zero_mul,Complex.exp_zero,norm_one,one_mul]

/-- Full phase-product descent on the selected open-angle domain for
ANY independent bounded phase with the opposite physical rotation law.
Only that selected angle must be open; other actions may all be closed. -/
theorem exists_opposite_unit_phase_action_factor (s : ℕ) (hs : 1 ≤ s)
    (m : ℕ) (hm : 1 ≤ m) (Q : MiuraRealSobolevSource s → ℂ)
    (hQ : ContinuousOn Q {a | miuraNativeNLSAngularCoordinate s m a ≠ 0})
    (hbound : ∀ a, ‖Q a‖ ≤ 1)
    (hflow : ∀ a : MiuraRealSobolevSource s, miuraNativeNLSAngularCoordinate s m a ≠ 0 →
      ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, Q (miuraNativeRealActionFlow s a n t) =
        Complex.exp (-(if m = n then I else 0)*(t : ℂ))*Q a) :
    ∃ f : MiuraNativeActionMeanTarget s → ℂ, ∀ a : MiuraRealSobolevSource s,
      f (miuraNativeActionMeanMap s a.val) = miuraNativeNLSUnitPhase s m a*Q a := by
  let U := miuraNativeNLSAngularCoordinate s m
  have hU := continuous_miuraNativeNLSAngularCoordinate s m
  have hprod : Continuous (fun a => U a*Q a) := continuous_mul_bounded_phase U Q hU hQ hbound
  have hprodflow : ∀ a n, 1 ≤ n → ∀ t : ℝ,
      U (miuraNativeRealActionFlow s a n t)*Q (miuraNativeRealActionFlow s a n t) = U a*Q a := by
    intro a n hn t
    have hu := miuraNativeNLSAngularCoordinate_actionFlow s m hm a n hn t
    change U (miuraNativeRealActionFlow s a n t) = Complex.exp ((if m = n then I else 0)*(t : ℂ))*U a at hu
    by_cases ha : U a = 0
    · rw [hu,ha,mul_zero,zero_mul,zero_mul]
    · rw [hu,hflow a ha n hn t]
      have hc : Complex.exp ((if m = n then I else 0)*(t : ℂ))*
          Complex.exp (-(if m = n then I else 0)*(t : ℂ)) = 1 := by
        rw [← Complex.exp_add,← add_mul,add_neg_cancel,zero_mul,Complex.exp_zero]
      linear_combination (U a*Q a)*hc
  obtain ⟨F,hF⟩ := exists_miuraContinuousObservable_action_factor s hs (fun a => U a*Q a) hprod hprodflow
  obtain ⟨A,hA⟩ := exists_miuraContinuousObservable_action_factor s hs (fun a => ‖U a‖) hU.norm
    (fun a n hn t => norm_miuraNativeNLSAngularCoordinate_actionFlow s m hm a n hn t)
  refine ⟨fun q => F q/(A q : ℂ),fun a => ?_⟩
  dsimp only
  rw [hF,hA]
  change U a*Q a/(‖U a‖ : ℂ) = (U a/(‖U a‖ : ℂ))*Q a
  ring

end NLS.MKdV
