import NLS.KdV.HillWeightedActionSequence
import NLS.SequenceSpaces.Multiplier

/-! # The actual raw positive Hill actions as a continuous ell1 sequence -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

def hillActionSequenceDenominator (w : SpectralWeight) (k : ℤ) : ℝ :=
  w (2*((Equiv.intEquivNat k+1 : ℕ) : ℤ))^2*(2*Real.pi*(Equiv.intEquivNat k+1 : ℕ))

theorem one_le_hillActionSequenceDenominator (w : SpectralWeight) (k : ℤ) :
    1 ≤ hillActionSequenceDenominator w k := by
  have hn : (1 : ℝ) ≤ (Equiv.intEquivNat k+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hw : 1 ≤ w (2*((Equiv.intEquivNat k+1 : ℕ) : ℤ))^2 := one_le_pow₀ (w.one_le _)
  have hp : 1 ≤ 2*Real.pi*(Equiv.intEquivNat k+1 : ℕ) := by nlinarith [Real.pi_gt_three]
  exact one_mul (1 : ℝ) ▸ mul_le_mul hw hp (by norm_num) (by positivity)

def hillInverseActionSequenceWeight (w : SpectralWeight) : Coeff ⊤ :=
  ⟨fun k => (hillActionSequenceDenominator w k : ℂ)⁻¹,memℓp_infty ⟨1,by
    rintro _ ⟨k,rfl⟩
    have hD := one_le_hillActionSequenceDenominator w k
    have hp : 0 < hillActionSequenceDenominator w k := by linarith
    change ‖(hillActionSequenceDenominator w k : ℂ)⁻¹‖ ≤ 1
    rw [norm_inv,norm_real,Real.norm_eq_abs,abs_of_pos hp]
    simpa only [one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1) hD⟩⟩

def hillRawActionSequence (w : SpectralWeight) (q : RealHillWeightedPotential w) : Coeff 1 :=
  Coeff.multiplierCLM (hillInverseActionSequenceWeight w) (hillWeightedActionSequence w q)

theorem hillRawActionSequence_apply (w : SpectralWeight) (q : RealHillWeightedPotential w) (k : ℤ) :
    hillRawActionSequence w q k = (hillPeriodOneAction w q.val q.property (Equiv.intEquivNat k+1) : ℂ) := by
  change (hillActionSequenceDenominator w k : ℂ)⁻¹*
    (hillWeightedActionTerm w q (Equiv.intEquivNat k+1) : ℂ) = _
  have he : hillWeightedActionTerm w q (Equiv.intEquivNat k+1) =
      hillActionSequenceDenominator w k*hillPeriodOneAction w q.val q.property (Equiv.intEquivNat k+1) := rfl
  rw [he,ofReal_mul,inv_mul_cancel_left₀]
  exact ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_hillActionSequenceDenominator w k)))

theorem continuous_hillRawActionSequence (w : SpectralWeight) : Continuous (hillRawActionSequence w) :=
  (Coeff.multiplierCLM (hillInverseActionSequenceWeight w)).continuous.comp (continuous_hillWeightedActionSequence w)

end NLS.KdV
