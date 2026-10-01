import NLS.ZakharovShabat.SourceAngularEtaIsospectralKernel
import NLS.ZakharovShabat.SourceDirichletDiscriminantKernel

/-! # The actual diagonal eta/discriminant kernel

The proved actual discriminant terminal flow supplies the general
isospectral eta calculation. The diagonal cotangent has the filled
Dirichlet kernel at every spectral parameter, including coincidence
and either periodic Dirichlet endpoint.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual eta cotangent on every actual open-gap chart has the
filled discriminant kernel, including periodic terminals. -/
theorem SourceAngularEtaAnalyticChartData.sourceBivector_etaDifferential_discriminant_eq_kernel
    {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
    {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
    {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R ρ : ℝ} {z₀ : ℂ} {δ ε : CoeffPair p → ℂ}
    (C : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ U) (hφ₀ : φ.val ∈ W₀) (w : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n
    sourceBivector h2p (sourceAngularEtaDifferential hp hp1 n s φ.val)
      (fderiv ℂ (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val) =
      sourcePsiCandidate n (μ,(s n φ.val : Coeff p))*sourceDirichletDiscriminantKernel hp hp1 n φ.val w := by
  let h := sourceHamiltonianVector h2p
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val
  have hiso : SourceIsospectralDirection hp φ.val h :=
    sourceHamiltonianVector_discriminant_isospectral hp hp1 h2p φ.val w
  have hroot := sourceBracket_dirichletRoot_discriminant_eq_kernel hp hp1 h2p n φ.val φ.property w
  have hanti := sourceBracket_dirichletTerminalAnti_discriminant_eq_kernel hp hp1 h2p n φ.val φ.property w
  rw [← fderiv_apply_sourceHamiltonianVector] at hroot hanti
  rw [← apply_sourceHamiltonianDirection]
  exact C.etaDifferential_isospectral_eq_kernel hs φ hφ hφ₀
    h hiso (sourceDirichletDiscriminantKernel hp hp1 n φ.val w) hroot hanti

/-- Actual common-domain charts supply the diagonal eta/discriminant
kernel at every real source with an open selected angle gap. -/
theorem SourceAngularThetaCommonDomainData.sourceBivector_etaDifferential_discriminant_eq_kernel
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
    {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (w : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n
    sourceBivector h2p (sourceAngularEtaDifferential hp hp1 n s φ.val)
      (fderiv ℂ (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val) =
      sourcePsiCandidate n (μ,(s n φ.val : Coeff p))*sourceDirichletDiscriminantKernel hp hp1 n φ.val w := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,_,_,C⟩ :=
    D.local_charts n φ.val (D.real_subset φ.property) hgap
  have hs := D.psi.toSourcePsiIsolatingComplexExtension
  obtain ⟨a,ha,_,_,_,_,hball,_,_,_,_⟩ := hs.isolation φ
  exact C.sourceBivector_etaDifferential_discriminant_eq_kernel hs h2p φ hφU
    (hball (mem_ball_self ha)) w

end NLS.ZakharovShabat
