import NLS.KdV.HminusOneDirichletSimplicity
import NLS.ComplexAnalysis.AnalyticImplicitScalarExistence

/-! Local analytic rough Dirichlet energies on the full complex original
H-minus-one potential space. Real-potential roots are all covered, including
low energies, because their simplicity has been proved independently. -/
noncomputable section
open Set Complex Filter
open scoped Topology
namespace NLS.KdV

/-- Any simple full H-minus-one Dirichlet zero has an actual local
analytic zero selection in the original complex potential norm. -/
theorem exists_local_analytic_hillHminusDirichlet_root
    (q : PeriodOneHminusOne) (lambda : ℂ) (hl : hillHminusDirichlet q lambda = 0)
    (hs : deriv (hillHminusDirichlet q) lambda ≠ 0) :
    ∃ mu : PeriodOneHminusOne → ℂ, AnalyticAt ℂ mu q ∧ mu q = lambda ∧
      ∀ᶠ p in 𝓝 q, hillHminusDirichlet p (mu p) = 0 := by
  let F : ℂ × PeriodOneHminusOne → ℂ := fun p => hillHminusDirichlet p.2 p.1
  have hF := analyticOnNhd_hillHminusDirichlet_joint (lambda,q) (mem_univ _)
  have hd := NLS.ComplexAnalysis.deriv_spectral_section_eq_fderiv F lambda q hF.differentiableAt
  have hn : (fderiv ℂ F (lambda,q)) (1,0) ≠ 0 := by
    rw [← hd]
    exact hs
  exact NLS.ComplexAnalysis.exists_analytic_implicitScalarRoot F lambda q hF hl hn

/-- Every Dirichlet zero at every real original H-minus-one potential
extends analytically under arbitrary sufficiently small COMPLEX perturbations. -/
theorem exists_local_analytic_hillHminusDirichlet_root_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ)
    (hl : hillHminusDirichlet q lambda = 0) :
    ∃ mu : PeriodOneHminusOne → ℂ, AnalyticAt ℂ mu q ∧ mu q = lambda ∧
      ∀ᶠ p in 𝓝 q, hillHminusDirichlet p (mu p) = 0 :=
  exists_local_analytic_hillHminusDirichlet_root q lambda hl
    (deriv_hillHminusDirichlet_ne_zero_of_real q hq lambda hl)

end NLS.KdV
