import NLS.ZakharovShabat.SourcePsiUniformComplexBranchRealAgreement
import NLS.ZakharovShabat.SourceHolomorphicRealCenteredBalls

/-!
# Compatibility of the uniform complex psi root branches

Branches centered at different real sources agree at every real source
in their overlap. The Banach-valued identity principle identifies them
throughout that overlap, independently of the chosen equation tubes.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePsiUniformComplexBranchFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}

theorem eqOn_sourceBall_overlap
    {φ₀ φ₁ : realTypeSourceLocus p}
    {D₀ : SourcePsiUniformEquationTube hp hp1 φ₀}
    {D₁ : SourcePsiUniformEquationTube hp hp1 φ₁}
    (S₀ : SourcePsiUniformComplexBranchFamily D₀)
    (S₁ : SourcePsiUniformComplexBranchFamily D₁) (n : ℤ) :
    EqOn (S₀.branch n) (S₁.branch n)
      (ball φ₀.val S₀.sourceRadius ∩ ball φ₁.val S₁.sourceRadius) := by
  apply eqOn_sourceRealCenteredBalls_of_real_agreement hp φ₀ φ₁
    S₀.sourceRadius S₁.sourceRadius (S₀.branch n) (S₁.branch n)
    (S₀.analytic n).differentiableOn (S₁.analytic n).differentiableOn
  intro χ hχ
  exact (S₀.eq_sourcePsiGapRoot_of_real n χ hχ.1).trans
    (S₁.eq_sourcePsiGapRoot_of_real n χ hχ.2).symm

end NLS.ZakharovShabat.SourcePsiUniformComplexBranchFamily
