import NLS.SequenceSpaces.PeriodOneFourierLebesgueMassResolvent

/-! # The exact native free mass equivalence at every Banach exponent -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal
namespace NLS

theorem norm_periodOneMassSymbol_le_linear (m : ℕ) (n : ℤ) :
    ‖periodOneMassSymbol m n‖≤((m : ℝ)+1+2*Real.pi)*(1+|(n : ℝ)|) := by
  have h : ‖periodOneMassSymbol m n‖≤((m : ℝ)+1)+2*Real.pi*|(n : ℝ)| := by
    calc
      _ ≤ ‖(((m : ℝ)+1 : ℝ) : ℂ)‖+‖2*I*(Real.pi : ℂ)*n‖ := norm_add_le _ _
      _ = _ := by
        simp only [norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg (show 0≤(m : ℝ)+1 by positivity),
          abs_of_pos Real.pi_pos,Complex.norm_intCast]
  exact h.trans (by nlinarith [Real.pi_pos,abs_nonneg (n : ℝ),show 0≤(m : ℝ) by positivity])

theorem periodOneMassSymbol_weighted_bound (m : ℕ) (s : ℝ) (n : ℤ) :
    Weight.sobolev s n*‖periodOneMassSymbol m n‖≤
      ((m : ℝ)+1+2*Real.pi)*Weight.sobolev (s+1) n := by
  rw [Weight.sobolev_add]
  change Weight.sobolev s n*‖periodOneMassSymbol m n‖≤
    ((m : ℝ)+1+2*Real.pi)*(Weight.sobolev s n*(1+|(n : ℝ)|)^((1 : ℝ)))
  rw [Real.rpow_one]
  calc
    _ ≤ Weight.sobolev s n*(((m : ℝ)+1+2*Real.pi)*(1+|(n : ℝ)|)) :=
      mul_le_mul_of_nonneg_left (norm_periodOneMassSymbol_le_linear m n) (Weight.positive _ n).le
    _ = _ := by ring

def periodOneFourierLebesgueMassOperator (m : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)] :
    WeightedCoeff (Weight.sobolev (s+1)) p →L[ℂ] WeightedCoeff (Weight.sobolev s) p :=
  WeightedCoeff.weightedMultiplierCLM _ _ (periodOneMassSymbol m) ((m : ℝ)+1+2*Real.pi)
    (by positivity) (periodOneMassSymbol_weighted_bound m s)

@[simp] theorem periodOneFourierLebesgueMassOperator_apply
    (m : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)]
    (a : WeightedCoeff (Weight.sobolev (s+1)) p) (n : ℤ) :
    (periodOneFourierLebesgueMassOperator m s p a).val n=periodOneMassSymbol m n*a.val n := rfl

/-- The actual unit-period mass symbol and its already-proved native
resolvent give inverse bounded maps, in BOTH original weighted lp norms. -/
def periodOneFourierLebesgueFreeMassEquiv (m : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)] :
    WeightedCoeff (Weight.sobolev (s+1)) p ≃L[ℂ] WeightedCoeff (Weight.sobolev s) p where
  toLinearEquiv := {
    toFun := periodOneFourierLebesgueMassOperator m s p
    invFun := periodOneFourierLebesgueMassInverse m s p
    left_inv := by
      intro a
      apply Subtype.ext
      funext n
      rw [periodOneFourierLebesgueMassInverse_apply,periodOneFourierLebesgueMassOperator_apply,
        inv_mul_cancel_left₀ (periodOneMassSymbol_ne_zero m n)]
    right_inv := by
      intro a
      apply Subtype.ext
      funext n
      rw [periodOneFourierLebesgueMassOperator_apply,periodOneFourierLebesgueMassInverse_apply,
        mul_inv_cancel_left₀ (periodOneMassSymbol_ne_zero m n)]
    map_add' := (periodOneFourierLebesgueMassOperator m s p).map_add
    map_smul' := (periodOneFourierLebesgueMassOperator m s p).map_smul }
  continuous_toFun := (periodOneFourierLebesgueMassOperator m s p).continuous
  continuous_invFun := (periodOneFourierLebesgueMassInverse m s p).continuous

@[simp] theorem periodOneFourierLebesgueFreeMassEquiv_apply
    (m : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)]
    (a : WeightedCoeff (Weight.sobolev (s+1)) p) :
    periodOneFourierLebesgueFreeMassEquiv m s p a=periodOneFourierLebesgueMassOperator m s p a := rfl

@[simp] theorem periodOneFourierLebesgueFreeMassEquiv_symm_apply
    (m : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)]
    (a : WeightedCoeff (Weight.sobolev s) p) :
    (periodOneFourierLebesgueFreeMassEquiv m s p).symm a=periodOneFourierLebesgueMassInverse m s p a := rfl

end NLS
