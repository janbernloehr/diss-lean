import NLS.Articles.KdVPseudomeasures.OriginalHillIntrinsicAbelianDivisor
import NLS.KdV.HillOnIndexPhysicalPhaseSquare

/-! Local physical diagonal Hill phase charts and their analytic
Cartesian factors. The diagonal period is removed explicitly only
from the remainder. Cosine-cover integration retains the ACTUAL
Hill differential and physical auxiliary Dirichlet sheet. Global
cross-Miura-patch gluing and infinite off-index sums are not asserted. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.KdV NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_onIndex_filled_remainder (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.onIndexAbelianFilledRemainder n)
      (ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) ×ˢ P.source) ∧
      ∀ q ∈ P.source, ∀ z ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)),
        sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) z*
          deriv (fun w => P.onIndexAbelianFilledRemainder n (w,q)) z+
        (z-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ))*P.onIndexAbelianFilledRemainder n (z,q) =
          P.abelianGapNumerator n n (z,q)-I :=
  ⟨P.analytic_onIndexAbelianFilledRemainder n,P.onIndexAbelianFilledRemainder_equation n⟩

theorem original_Hill_onIndex_cosine_phase_endpoint_normalization (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (δ : ℂ) :
    P.onIndexAbelianCosinePhase n q δ (Real.pi:ℂ) = 0 ∧
      P.onIndexAbelianCosinePhase n q δ 0 = -(Real.pi:ℂ) :=
  ⟨P.onIndexAbelianCosinePhase_at_pi n q δ,P.onIndexAbelianCosinePhase_at_zero n q δ⟩

theorem original_Hill_local_onIndex_Cartesian_extension (P : HillProductEquationPatch) :
    ∀ n : ℕ+, AnalyticOnNhd ℂ (P.physicalOnIndexCartesianPlus n) P.physicalDirichletSource ∧
      AnalyticOnNhd ℂ (P.physicalOnIndexCartesianMinus n) P.physicalDirichletSource ∧
      ∀ q ∈ P.physicalDirichletSource,
        P.physicalOnIndexCartesianPlus n q*P.physicalOnIndexCartesianMinus n q = hillHminusCanonicalGapSquare n q :=
  fun n => ⟨P.analytic_physicalOnIndexCartesianPlus n,P.analytic_physicalOnIndexCartesianMinus n,
    P.physicalOnIndexCartesian_product_eq_original_gap_square n⟩

theorem original_Hill_local_onIndex_phase_mod_pi_analytic (P : HillProductEquationPatch) (n : ℕ+) :
    IsOpen {q | q ∈ P.physicalDirichletSource ∧ hillHminusCanonicalGapSquare n q ≠ 0} ∧
      AnalyticOnNhd ℂ (P.physicalOnIndexPhaseSquare n)
        {q | q ∈ P.physicalDirichletSource ∧ hillHminusCanonicalGapSquare n q ≠ 0} ∧
      ∀ q ∈ P.physicalDirichletSource, hillHminusCanonicalGapSquare n q ≠ 0 → P.physicalOnIndexPhaseSquare n q ≠ 0 :=
  ⟨P.isOpen_physicalOnIndexPhaseDomain n,P.analytic_physicalOnIndexPhaseSquare n,P.physicalOnIndexPhaseSquare_ne_zero n⟩

theorem original_Hill_actual_physical_onIndex_phase_chart (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (hgap : hillHminusCanonicalGapSquare n q ≠ 0) :
    ∃ δ ε α : PeriodOneHminusOne → ℂ, AnalyticAt ℂ δ q ∧ AnalyticAt ℂ ε q ∧ AnalyticAt ℂ α q ∧ δ q ≠ 0 ∧
      ∀ᶠ a in 𝓝 q, a ∈ P.physicalDirichletSource ∧
        δ a^2 = (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4 ∧
        cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)) (δ a) (ε a) =
          P.physicalDirichletFrequency ((n:ℕ):ℤ) a ∧
        -I*δ a*Complex.sin (ε a) = P.physicalDirichletRootCoefficient n a ∧
        α a = P.onIndexAbelianCosinePhase n a (δ a) (ε a) ∧
        α a = ε a-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n a :=
  P.exists_analytic_physical_onIndex_phase_chart n q hq
    (P.frequency_half_gap_square_ne_zero_of_original_gap n q hq hgap)

end NLS.Articles.KdVPseudomeasures
