import NLS.KdV.HillDirichletGardnerCommutation
import NLS.KdV.HminusOneCanonicalDirichlet
import NLS.ComplexAnalysis.ImplicitScalarRootDerivative
import NLS.Poisson.GardnerHamiltonianDirection

/-! Actual labelled simple Dirichlet eigenvalues have the full implicit
source derivative and Gardner-commute on their unchanged common complex
domain. No distinctness, open-gap or real-source assumption is needed. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem fderiv_hillHminusCanonicalDirichlet_eq_characteristic
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    fderiv ℂ (hillHminusCanonicalDirichlet n) q=
      -(deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q))⁻¹ •
        fderiv ℂ (fun p => hillHminusDirichlet p (hillHminusCanonicalDirichlet n q)) q := by
  let F : ℂ × PeriodOneHminusOne → ℂ := fun t => hillHminusDirichlet t.2 t.1
  have hF := (analyticOnNhd_hillHminusDirichlet_joint (hillHminusCanonicalDirichlet n q,q) (mem_univ _)).differentiableAt
  have hs := (analyticOnNhd_hillHminusCanonicalDirichlet n q hq).differentiableAt
  have hzero : ∀ᶠ p in 𝓝 q, F (hillHminusCanonicalDirichlet n p,p)=0 := by
    filter_upwards [isOpen_hillHminusCanonicalDirichletDomain.mem_nhds hq] with p hp
    exact hillHminusCanonicalDirichlet_is_root n p hp
  have hspec : (fderiv ℂ F (hillHminusCanonicalDirichlet n q,q)) (1,0)=
      deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q) :=
    (deriv_spectral_section_eq_fderiv F _ q hF).symm
  have hne : (fderiv ℂ F (hillHminusCanonicalDirichlet n q,q)) (1,0) ≠ 0 := by
    rw [hspec]
    exact deriv_hillHminusCanonicalDirichlet_ne_zero n q hq
  ext h
  have hb := implicitScalarRoot_fderiv_apply F (hillHminusCanonicalDirichlet n) q h hF hs hzero hne
  change (fderiv ℂ (hillHminusCanonicalDirichlet n) q) h=
    -(fderiv ℂ (fun p => hillHminusDirichlet p (hillHminusCanonicalDirichlet n q)) q) h / _ at hb
  rw [hb,hspec]
  simp only [smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

theorem hillHminusCanonicalDirichlets_Gardner_commute
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusCanonicalDirichlet m) q=0 := by
  change NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (hillHminusCanonicalDirichlet n) q)
    (fderiv ℂ (hillHminusCanonicalDirichlet m) q)=0
  rw [fderiv_hillHminusCanonicalDirichlet_eq_characteristic n q hq,
    fderiv_hillHminusCanonicalDirichlet_eq_characteristic m q hq]
  have hz : NLS.Poisson.gardnerCotangentBivector
      (fderiv ℂ (fun p => hillHminusDirichlet p (hillHminusCanonicalDirichlet n q)) q)
      (fderiv ℂ (fun p => hillHminusDirichlet p (hillHminusCanonicalDirichlet m q)) q)=0 :=
    hillHminusDirichletCharacteristics_Gardner_commute q _ _
  simp only [map_smul,smul_apply,hz,smul_zero]

end NLS.KdV
