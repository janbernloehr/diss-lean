import NLS.Articles.KdVPseudomeasures.OriginalHillDirichletGardner
import NLS.Articles.KdVPseudomeasures.OriginalHillActionInvolution
import NLS.KdV.HillLocalLogNormingGardner
import NLS.KdV.HillActionDirichletContour

/-! Original spectral cross brackets and the actual action/Dirichlet
contour. The local logarithm is a spectral auxiliary, not a replacement
for the article's Abelian angle or signed Birkhoff coordinates. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

theorem original_Hill_Dirichlet_norming_Gardner_matrix
    (q : OriginalHminusOnePotential) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusDirichletNorming m)
      (originalPeriodOneCoefficients q)=
      (if n=m then -hillHminusDirichletNorming m (originalPeriodOneCoefficients q)/2 else 0) :=
  hillHminus_Dirichlet_norming_Gardner_matrix n m _
    (real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q))

theorem original_Hill_Dirichlet_localLogNorming_Gardner_matrix
    (q : OriginalHminusOnePotential) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n)
      (hillHminusLocalLogNorming m (originalPeriodOneCoefficients q)) (originalPeriodOneCoefficients q)=
      (if n=m then 1 else 0) :=
  hillHminus_Dirichlet_localLogNorming_Gardner_at_base n m _
    (real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q))

theorem original_Hill_resonant_discriminant_Dirichlet_Gardner
    (q : OriginalHminusOnePotential) (n : ℕ+) :
    2*NLS.Poisson.hminusGardnerBracket
      (fun p => hillHminusDiscriminant p (hillHminusCanonicalDirichlet n (originalPeriodOneCoefficients q)))
      (hillHminusCanonicalDirichlet n) (originalPeriodOneCoefficients q)=
      -hillHminusDirichletSheet n (originalPeriodOneCoefficients q) :=
  hillHminus_resonant_discriminant_Dirichlet_Gardner n _
    (real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q))

theorem exists_original_Hill_action_Dirichlet_bracket_contour
    (q : OriginalHminusOnePotential) (m n : ℕ+) :
    ∃ u : Coeff 2, ∃ c : ℂ,
      periodOneMiura u=originalPeriodOneCoefficients q+periodOneL2Inclusion (lp.single 2 0 c) ∧
      ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧
        CircleIntegrable (hillMiuraActionDirichletIntegrand n (originalPeriodOneCoefficients q) u c) a R ∧
        deriv (hillHminusDirichlet (originalPeriodOneCoefficients q))
          (hillHminusCanonicalDirichlet n (originalPeriodOneCoefficients q))*
          NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction m) (hillHminusCanonicalDirichlet n)
            (originalPeriodOneCoefficients q)=
          hillHminusDirichletSheet n (originalPeriodOneCoefficients q)*(Real.pi : ℂ)⁻¹*
            (∮ z in C(a,R), hillMiuraActionDirichletIntegrand n (originalPeriodOneCoefficients q) u c z) :=
  exists_hillHminus_action_Dirichlet_bracket_contour _ (originalPeriodOneCoefficients_real q) m n

end NLS.Articles.KdVPseudomeasures
