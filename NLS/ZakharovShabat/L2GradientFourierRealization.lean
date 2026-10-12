import NLS.ZakharovShabat.L2GradientComparison
import NLS.ZakharovShabat.SourceCorollaryG6
import NLS.Fourier.IntervalCoefficientLinearity

/-! # Actual physical gradients in the signed source Fourier coordinates

Realization records the ordinary Fourier integrals, the factor i, and
the original first-index reversal. A coefficient vector supplies its
actual finite-exponent source norm; no norm of a divergent sum is used.
-/
noncomputable section
open scoped ENNReal
open Set Complex NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

/-- The exact source convention for i times a two-component physical gradient. -/
def L2GradientFourierRealizes {q : ℝ≥0∞} (g : ℝ → ℂ × ℂ) (a : CoeffPair q) : Prop :=
  ∀ k : ℤ, a.fst k = I*intervalFourierCoefficient 1 (fun s => (g s).1) (-k) ∧
    a.snd k = I*intervalFourierCoefficient 1 (fun s => (g s).2) k

theorem L2GradientFourierRealizes.unique {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {g : ℝ → ℂ × ℂ} {a b : CoeffPair q} (ha : L2GradientFourierRealizes g a)
    (hb : L2GradientFourierRealizes g b) : a = b := by
  apply (CoeffPair.toMax q).injective
  apply Prod.ext
  · ext k
    exact (ha k).1.trans (hb k).1.symm
  · ext k
    exact (ha k).2.trans (hb k).2.symm

/-- The realized vector has exactly equation (1.2)'s combined coefficient energy. -/
theorem L2GradientFourierRealizes.norm_rpow {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    {g : ℝ → ℂ × ℂ} {a : CoeffPair q} (ha : L2GradientFourierRealizes g a) :
    ‖a‖^q.toReal = ∑' k : ℤ,
      (‖intervalFourierCoefficient 1 (fun s => (g s).1) (-k)‖^q.toReal+
       ‖intervalFourierCoefficient 1 (fun s => (g s).2) k‖^q.toReal) := by
  rw [CoeffPair.norm_rpow_eq_tsum hq]
  apply tsum_congr
  intro k
  rw [(ha k).1,(ha k).2]
  simp only [norm_mul,norm_I,one_mul]

/-- The established discriminant coefficients are actual physical L2 gradient coefficients. -/
theorem sourceG6DiscriminantCoefficients_realizes_l2 {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    L2GradientFourierRealizes (l2DiscriminantGradient (continuousPotentialL2Class Φ) z)
      (sourceG6DiscriminantCoefficients hq Φ z) := by
  intro k
  rw [sourceG6DiscriminantCoefficients_fst,sourceG6DiscriminantCoefficients_snd]
  constructor <;> congr 1
  · apply intervalFourierCoefficient_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    exact congrArg Prod.fst (l2DiscriminantGradient_of_continuous Φ z ⟨s,hs'⟩).symm
  · apply intervalFourierCoefficient_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    exact congrArg Prod.snd (l2DiscriminantGradient_of_continuous Φ z ⟨s,hs'⟩).symm

/-- The anti-discriminant coefficients subtract the actual free L2 gradient. -/
theorem sourceG6AntiDiscriminantCoefficients_realizes_l2 {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    L2GradientFourierRealizes (l2AntiDiscriminantGradientRemainder (continuousPotentialL2Class Φ) z w)
      (sourceG6AntiDiscriminantCoefficients hq Φ z w) := by
  intro k
  rw [sourceG6AntiDiscriminantCoefficients_fst,sourceG6AntiDiscriminantCoefficients_snd]
  constructor <;> congr 1
  · apply intervalFourierCoefficient_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    exact congrArg Prod.fst (l2AntiDiscriminantGradientRemainder_of_continuous Φ z w ⟨s,hs'⟩).symm
  · apply intervalFourierCoefficient_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    exact congrArg Prod.snd (l2AntiDiscriminantGradientRemainder_of_continuous Φ z w ⟨s,hs'⟩).symm

end NLS.ZakharovShabat
