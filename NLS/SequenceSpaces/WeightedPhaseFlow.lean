import NLS.SequenceSpaces.Weighted
import NLS.SequenceSpaces.PhaseRotation

/-! # Isometric phase evolution in weighted Fourier spaces

Arbitrary real frequencies, including the quadratic Schrödinger frequencies,
give a strongly continuous group at every finite exponent. No boundedness of
the frequency sequence is needed.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Diagonal unit phases transported through the weighted coefficient isometry. -/
def phaseFlow (w : Weight) (freq : ℤ → ℝ) (time : ℝ) :
    WeightedCoeff w p →ₗᵢ[ℂ] WeightedCoeff w p :=
  (weightIsometry w p).symm.toLinearIsometry.comp
    ((Coeff.phaseFlow freq time).comp (weightIsometry w p).toLinearIsometry)

@[simp] theorem phaseFlow_apply (w : Weight) (freq : ℤ → ℝ) (time : ℝ)
    (a : WeightedCoeff w p) (n : ℤ) :
    (phaseFlow w freq time a).val n = Complex.exp (((time*freq n : ℝ) : ℂ)*Complex.I)*a.val n := by
  change (Complex.exp _ * ((w n : ℂ)*a.val n)) / (w n : ℂ) = _
  rw [mul_left_comm, mul_div_cancel_left₀ _ (w.complex_ne_zero n)]

@[simp] theorem phaseFlow_zero (w : Weight) (freq : ℤ → ℝ) (a : WeightedCoeff w p) :
    phaseFlow w freq 0 a = a := by
  apply Subtype.ext
  funext n
  simp

/-- The group identity holds in the full weighted Banach space. -/
theorem phaseFlow_add (w : Weight) (freq : ℤ → ℝ) (time r : ℝ) (a : WeightedCoeff w p) :
    phaseFlow w freq time (phaseFlow w freq r a) = phaseFlow w freq (time+r) a := by
  apply Subtype.ext
  funext n
  simp only [phaseFlow_apply,add_mul,Complex.ofReal_add,Complex.exp_add]
  ring

@[simp] theorem norm_phaseFlow (w : Weight) (freq : ℤ → ℝ) (time : ℝ) (a : WeightedCoeff w p) :
    ‖phaseFlow w freq time a‖ = ‖a‖ := (phaseFlow w freq time).norm_map a

/-- Joint strong continuity survives weighting. -/
theorem continuous_phaseFlow (w : Weight) (hp : p ≠ ⊤) (freq : ℤ → ℝ) :
    Continuous (fun x : ℝ × WeightedCoeff w p => phaseFlow w freq x.1 x.2) := by
  exact (weightIsometry w p).symm.continuous.comp
    ((Coeff.continuous_phaseFlow hp freq).comp
      (continuous_fst.prodMk ((weightIsometry w p).continuous.comp continuous_snd)))

end NLS.WeightedCoeff
