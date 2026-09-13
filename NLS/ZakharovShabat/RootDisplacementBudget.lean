import NLS.ZakharovShabat.DiagonalSummability
import NLS.ZakharovShabat.OffDiagonalSummability

/-!
# The corrected displacement budget

The additive leading-tail term is retained outside the nonlinear
potential-norm factors. All constants depend only on the exponent.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- An exponent-only constant for the corrected two-root displacement estimate. -/
def rootDisplacementSummationConstant (p : ℝ≥0∞) : ℝ :=
  (2*(2 : ℝ)^(p.toReal-1)+((2 : ℝ)^(p.toReal-1))^2) *
    (1+diagonalSummationConstant p+offDiagonalSummationConstant p)

theorem rootDisplacementSummationConstant_nonneg (p : ℝ≥0∞) :
    0 ≤ rootDisplacementSummationConstant p := by
  have hd := diagonalSummationConstant_nonneg (p := p)
  have he := offDiagonalSummationConstant_nonneg p
  unfold rootDisplacementSummationConstant
  positivity

/-- Scalar combination of the diagonal, leading, and cubic remainder budgets. -/
theorem combine_rootDisplacement_budgets {A T D K Cd Ce : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hTA : T ≤ A) (hD : 0 ≤ D)
    (hK : 0 ≤ K) (hd : 0 ≤ Cd) (he : 0 ≤ Ce) :
    2*K*(Cd*A*(A/D+T)+K/2*(T+Ce*A*(A^2/D+T^2))) ≤
      (2*K+K^2)*(1+Cd+Ce)*(T+(A/D+T)*(1+A)*A) := by
  let H := (A/D+T)*(1+A)*A
  have hL : 0 ≤ A/D+T := by positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hdiag : A*(A/D+T) ≤ H := by
    dsimp [H]
    nlinarith [mul_nonneg hA hL]
  have hT2 : T^2 ≤ A*T := by nlinarith
  have hoff : A*(A^2/D+T^2) ≤ H := by
    have hh : A*(A^2/D+T^2) ≤ A^2*(A/D+T) := by
      calc
        _ ≤ A*(A^2/D+A*T) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hT2) hA
        _ = _ := by ring
    apply hh.trans
    dsimp [H]
    nlinarith [mul_nonneg hA hL]
  have hd' : Cd*A*(A/D+T) ≤ (1+Cd+Ce)*(T+H) := by
    calc
      _ = Cd*(A*(A/D+T)) := by ring
      _ ≤ Cd*H := mul_le_mul_of_nonneg_left hdiag hd
      _ ≤ (1+Cd+Ce)*(T+H) := by gcongr <;> linarith
  have he' : T+Ce*A*(A^2/D+T^2) ≤ (1+Cd+Ce)*(T+H) := by
    have hb : Ce*A*(A^2/D+T^2) ≤ Ce*H := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hoff he
    calc
      _ ≤ T+Ce*H := add_le_add le_rfl hb
      _ ≤ (1+Cd+Ce)*(T+H) := by
        nlinarith [mul_nonneg hd hT, mul_nonneg hd hH, mul_nonneg he hT]
  calc
    _ ≤ 2*K*((1+Cd+Ce)*(T+H)+K/2*((1+Cd+Ce)*(T+H))) := by gcongr
    _ = _ := by dsimp [H]; ring

/-- The corrected budget adds the leading Fourier tail to the source nonlinear expression. -/
def rootDisplacementBudget {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) : ℝ :=
  rootDisplacementSummationConstant p *
    (‖weightedPairFourierTail w.toWeight (N/2) φ‖^p.toReal +
      (‖φ‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight (N/2) φ‖^p.toReal) *
        (1+‖φ‖^p.toReal)*‖φ‖^p.toReal)

end NLS.ZakharovShabat
