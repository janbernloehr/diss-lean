import NLS.Poisson.SobolevCommonState
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # The Section 2 bracket at a common physical state

Analytic functionals on reciprocal Sobolev source domains have automatically
compatible full gradients when both conjugate source exponents are finite.
Their bracket is defined on the entire intersection, with the printed -iJ
formula, an absolutely convergent Fourier sum, and analytic dependence on
the common state. No Hilbert regularity assumption is added.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Poisson
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The left full gradient, normalized to Sobolev order s without changing raw coefficients. -/
def commonLeftGradient (s : ℝ) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ) (x : SobolevCommonState s p q) :
    WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p :=
  negNegComponents s (WeightedCoeffPair.sobolevCotangentComponentsCLM (-s) hq (fderiv ℂ F x.val.1))

/-- The right full gradient lies at the reciprocal Sobolev order and exponent. -/
def commonRightGradient (s : ℝ) (hp : p ≠ ⊤)
    (G : WeightedCoeffPair (Weight.sobolev s) p → ℂ) (x : SobolevCommonState s p q) :
    WeightedCoeff (Weight.sobolev (-s)) q × WeightedCoeff (Weight.sobolev (-s)) q :=
  WeightedCoeffPair.sobolevCotangentComponentsCLM s hp (fderiv ℂ G x.val.2)

/-- The printed bracket evaluated on the same physical state in both source domains. -/
def commonSobolevBracket (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ)
    (G : WeightedCoeffPair (Weight.sobolev s) p → ℂ) (x : SobolevCommonState s p q) : ℂ :=
  conjugateBivector s hp hq (fderiv ℂ F x.val.1) (fderiv ℂ G x.val.2)

/-- The source's -iJ formula in actual scalar Fourier coordinates. -/
theorem commonSobolevBracket_physical (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ)
    (G : WeightedCoeffPair (Weight.sobolev s) p → ℂ) (x : SobolevCommonState s p q) :
    let a := commonLeftGradient s hq F x
    let b := commonRightGradient s hp G x
    commonSobolevBracket s hp hq F G x = -Complex.I *
      (WeightedCoeff.sobolevBilinearPairing s (WeightedCoeff.reflection s a.1) b.2 -
        WeightedCoeff.sobolevBilinearPairing s a.2 (WeightedCoeff.reflection (-s) b.1)) :=
  signedBivector_physical s _ _

/-- Automatic absolute convergence for the full recovered gradients. -/
theorem commonSobolevBracket_summable (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ)
    (G : WeightedCoeffPair (Weight.sobolev s) p → ℂ) (x : SobolevCommonState s p q) :
    let a := commonLeftGradient s hq F x
    let b := commonRightGradient s hp G x
    Summable (fun n : ℤ => ‖a.1.val n*b.2.val n-a.2.val n*b.1.val n‖) :=
  summable_signed_cross s _ _

/-- The actual, absolutely convergent signed-frequency formula. -/
theorem commonSobolevBracket_eq_tsum (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ)
    (G : WeightedCoeffPair (Weight.sobolev s) p → ℂ) (x : SobolevCommonState s p q) :
    let a := commonLeftGradient s hq F x
    let b := commonRightGradient s hp G x
    commonSobolevBracket s hp hq F G x = -Complex.I * ∑' n : ℤ,
      (a.1.val n*b.2.val n-a.2.val n*b.1.val n) :=
  signedBivector_eq_tsum s _ _

theorem norm_commonSobolevBracket_le (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ)
    (G : WeightedCoeffPair (Weight.sobolev s) p → ℂ) (x : SobolevCommonState s p q) :
    ‖commonSobolevBracket s hp hq F G x‖ ≤ 2*‖fderiv ℂ F x.val.1‖*‖fderiv ℂ G x.val.2‖ :=
  norm_conjugateBivector_le s hp hq _ _

/-- Analyticity on the full common-state domain, without choosing a smoother subspace. -/
theorem analyticOnNhd_commonSobolevBracket (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ)
    (G : WeightedCoeffPair (Weight.sobolev s) p → ℂ)
    {UF : Set (WeightedCoeffPair (Weight.sobolev (-s)) q)}
    {UG : Set (WeightedCoeffPair (Weight.sobolev s) p)}
    (hF : AnalyticOnNhd ℂ F UF) (hG : AnalyticOnNhd ℂ G UG) :
    AnalyticOnNhd ℂ (commonSobolevBracket s hp hq F G)
      {x : SobolevCommonState s p q | x.val.1 ∈ UF ∧ x.val.2 ∈ UG} := by
  intro x hx
  exact ((conjugateBivector s hp hq).analyticAt_bilinear _).comp₂
    ((hF.fderiv x.val.1 hx.1).comp (f := commonStateLeftCLM (p := p) (q := q) s) (x := x)
      ((commonStateLeftCLM s).analyticAt x))
    ((hG.fderiv x.val.2 hx.2).comp (f := commonStateRightCLM (p := p) (q := q) s) (x := x)
      ((commonStateRightCLM s).analyticAt x))

/-- The original scalar product rule on the first source domain. -/
theorem commonSobolevBracket_mul_left (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F H : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ)
    (G : WeightedCoeffPair (Weight.sobolev s) p → ℂ) (x : SobolevCommonState s p q)
    (hF : DifferentiableAt ℂ F x.val.1) (hH : DifferentiableAt ℂ H x.val.1) :
    commonSobolevBracket s hp hq (fun y => F y*H y) G x =
      F x.val.1*commonSobolevBracket s hp hq H G x + H x.val.1*commonSobolevBracket s hp hq F G x := by
  rw [commonSobolevBracket,fderiv_fun_mul hF hH]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rfl

/-- The normalized left gradient represents the full original differential on every direction. -/
theorem commonLeftGradient_represents (s : ℝ) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ) (x : SobolevCommonState s p q)
    (h : WeightedCoeffPair (Weight.sobolev (-s)) q) :
    let a := commonLeftGradient s hq F x
    fderiv ℂ F x.val.1 h = (∑' n : ℤ, h.fst.val n*a.1.val (-n)) +
      ∑' n : ℤ, h.snd.val n*a.2.val (-n) := by
  have he := WeightedCoeffPair.sobolevBilinearPairing_cotangentComponents (q := p) (-s) hq (fderiv ℂ F x.val.1) h
  simpa only [commonLeftGradient,negNegComponents_fst_val,negNegComponents_snd_val,
    WeightedCoeff.sobolevBilinearPairing_apply] using he.symm

/-- The right gradient also represents the full original differential on its own entire domain. -/
theorem commonRightGradient_represents (s : ℝ) (hp : p ≠ ⊤)
    (G : WeightedCoeffPair (Weight.sobolev s) p → ℂ) (x : SobolevCommonState s p q)
    (h : WeightedCoeffPair (Weight.sobolev s) p) :
    let b := commonRightGradient s hp G x
    fderiv ℂ G x.val.2 h = (∑' n : ℤ, h.fst.val n*b.1.val (-n)) +
      ∑' n : ℤ, h.snd.val n*b.2.val (-n) := by
  have he := WeightedCoeffPair.sobolevBilinearPairing_cotangentComponents (q := q) s hp (fderiv ℂ G x.val.2) h
  simpa only [commonRightGradient,WeightedCoeff.sobolevBilinearPairing_apply] using he.symm

end NLS.Poisson
