import NLS.Poisson.SourceBivector
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Poisson brackets of source functionals

The source bivector applied to the two Frechet differentials gives a
well-defined bracket for analytic functionals at exponents at least two.
It is analytic, antisymmetric, obeys the product rule, and is preserved
when the functionals are restricted along coefficient-preserving
exponent inclusions.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceBracket (h2p : (2:ℝ≥0∞) ≤ p) (F G : CoeffPair p → ℂ) (ψ : CoeffPair p) : ℂ :=
  sourceBivector h2p (fderiv ℂ F ψ) (fderiv ℂ G ψ)

theorem sourceBracket_antisymm (h2p : (2:ℝ≥0∞) ≤ p) (F G : CoeffPair p → ℂ) (ψ : CoeffPair p) :
    sourceBracket h2p F G ψ = -sourceBracket h2p G F ψ := sourceBivector_antisymm _ _ _

@[simp] theorem sourceBracket_self (h2p : (2:ℝ≥0∞) ≤ p) (F : CoeffPair p → ℂ) (ψ : CoeffPair p) :
    sourceBracket h2p F F ψ = 0 := sourceBivector_self _ _

theorem norm_sourceBracket_le (h2p : (2:ℝ≥0∞) ≤ p) (F G : CoeffPair p → ℂ) (ψ : CoeffPair p) :
    ‖sourceBracket h2p F G ψ‖ ≤ 2*‖fderiv ℂ F ψ‖*‖fderiv ℂ G ψ‖ := norm_sourceBivector_le _ _ _

theorem analyticOnNhd_sourceBracket (h2p : (2:ℝ≥0∞) ≤ p)
    {F G : CoeffPair p → ℂ} {U : Set (CoeffPair p)}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℂ (sourceBracket h2p F G) U := by
  intro ψ hψ
  exact ((sourceBivector h2p).analyticAt_bilinear _).comp₂ (hF.fderiv ψ hψ) (hG.fderiv ψ hψ)

theorem sourceBracket_mul_left (h2p : (2:ℝ≥0∞) ≤ p)
    (F H G : CoeffPair p → ℂ) (ψ : CoeffPair p)
    (hF : DifferentiableAt ℂ F ψ) (hH : DifferentiableAt ℂ H ψ) :
    sourceBracket h2p (fun χ => F χ*H χ) G ψ =
      F ψ*sourceBracket h2p H G ψ+H ψ*sourceBracket h2p F G ψ := by
  rw [sourceBracket,fderiv_fun_mul hF hH]
  simp only [map_add,map_smul,add_apply,
    smul_apply,smul_eq_mul]
  rfl

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem sourceBracket_restrict_exponent (h2p : (2:ℝ≥0∞) ≤ p) (hpq : p ≤ q)
    (F G : CoeffPair q → ℂ) (ψ : CoeffPair p)
    (hF : DifferentiableAt ℂ F (CoeffPair.exponentInclusion hpq ψ))
    (hG : DifferentiableAt ℂ G (CoeffPair.exponentInclusion hpq ψ)) :
    sourceBracket h2p (F ∘ CoeffPair.exponentInclusion hpq) (G ∘ CoeffPair.exponentInclusion hpq) ψ =
      sourceBracket (h2p.trans hpq) F G (CoeffPair.exponentInclusion hpq ψ) := by
  simp only [sourceBracket,fderiv_comp ψ hF (CoeffPair.exponentInclusion hpq).differentiableAt,
    fderiv_comp ψ hG (CoeffPair.exponentInclusion hpq).differentiableAt,
    ContinuousLinearMap.fderiv]
  exact sourceBivector_restrict_exponent _ _ _ _

end NLS.Poisson
