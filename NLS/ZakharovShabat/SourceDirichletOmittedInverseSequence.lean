import NLS.ZakharovShabat.SourceDirichletOmittedNormalizedAnalytic
import NLS.SequenceSpaces.NormalizedInverseAnalytic
import NLS.SequenceSpaces.AnalyticPhaseTrajectory
import NLS.SequenceSpaces.ExponentEmbedding

/-! The actual inverse omitted-product samples form an analytic bounded
sequence on the unchanged original angular domain. The normalization
error remains analytic in the original finite coefficient exponent. -/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The inverse of the normalized omitted product, minus its free value. -/
def sourceDirichletOmittedInverseError (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff p :=
  Coeff.ofFunctionOrZero p (fun n => (sourceDirichletOmittedNormalized hp hp1 ψ n)⁻¹-1)

/-- The bounded free parity sequence on both signed tails. -/
def sourceDirichletParitySymbol : Coeff ⊤ :=
  ⟨fun n => (-1 : ℂ)^n.natAbs, by
    apply memℓp_infty
    refine ⟨1, ?_⟩
    rintro _ ⟨n,rfl⟩
    simp⟩

/-- The inverse omitted-product symbol, realized through its normalized error. -/
def sourceDirichletOmittedInverseSymbol (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff ⊤ :=
  Coeff.multiplierCLM sourceDirichletParitySymbol
    (1+Coeff.exponentInclusion le_top (sourceDirichletOmittedInverseError hp hp1 ψ))

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Inversion preserves the original finite-exponent analytic normalization
on exactly the original angular domain, including every central index. -/
theorem dirichlet_omitted_inverse_error_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    AnalyticOnNhd ℂ (sourceDirichletOmittedInverseError hp hp1) W ∧
      ∀ ψ ∈ W, ∀ n, sourceDirichletOmittedInverseError hp hp1 ψ n =
        (sourceDirichletOmittedNormalized hp hp1 ψ n)⁻¹-1 := by
  obtain ⟨ha,he⟩ := H.dirichlet_omitted_normalized_analytic
  exact Coeff.analytic_normalized_inverse_error hp
    H.original_theta_common_domain.source_open (sourceDirichletOmittedNormalized hp hp1)
    (fun n ψ hψ => analyticAt_const.mul (H.dirichlet_omitted_sample_data ψ hψ n).2)
    (fun ψ hψ n => mul_ne_zero (pow_ne_zero _ (by norm_num))
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ _ n
        (H.dirichlet_omitted_sample_data ψ hψ n).1))
    _ ha.continuousOn he

/-- Every coordinate is the actual reciprocal, with its original sign. -/
theorem dirichlet_omitted_inverse_symbol_apply (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    sourceDirichletOmittedInverseSymbol hp hp1 ψ n =
      (sourceStandardRootOmittedProduct hp hp1 n ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))⁻¹ := by
  change (-1 : ℂ)^n.natAbs *
    (1+sourceDirichletOmittedInverseError hp hp1 ψ n) = _
  rw [H.dirichlet_omitted_inverse_error_analytic.2 ψ hψ n]
  rw [show 1+((sourceDirichletOmittedNormalized hp hp1 ψ n)⁻¹-1) =
    (sourceDirichletOmittedNormalized hp hp1 ψ n)⁻¹ by ring]
  simp only [sourceDirichletOmittedNormalized,mul_inv_rev]
  calc
    _ = ((-1 : ℂ)^n.natAbs * ((-1 : ℂ)^n.natAbs)⁻¹) *
        (sourceStandardRootOmittedProduct hp hp1 n ψ
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ (by norm_num)),one_mul]

/-- The complete actual inverse sequence is Banach analytic in the
bounded-sequence norm, on the unchanged complex source domain. -/
theorem dirichlet_omitted_inverse_symbol_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    AnalyticOnNhd ℂ (sourceDirichletOmittedInverseSymbol hp hp1) W := by
  intro ψ hψ
  exact ((Coeff.multiplierCLM (p := ⊤) sourceDirichletParitySymbol).analyticAt _).comp
    (analyticAt_const.add
      (((Coeff.exponentInclusion (show p ≤ ⊤ from le_top)).analyticAt _).comp
        (H.dirichlet_omitted_inverse_error_analytic.1 ψ hψ)))

end SourceLemma12_12Data
end NLS.ZakharovShabat
