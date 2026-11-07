import NLS.KdV.HillNativeNormingFirstVariation
import NLS.FunctionalAnalysis.LinearMovingSpectralDerivative

/-! Actual local Wiener comparison of the moving native multiplier,
with its full restricted source derivative at every base potential. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem hillHminusDirichletNorming_L1_eventually_eq_at
    (n : ℕ+) (a : Coeff 1) (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) :
    (fun b => hillHminusDirichletNorming n (periodOneL1Inclusion b)) =ᶠ[𝓝 a]
      (fun b => hillL1TerminalFamily (hillL1CanonicalDirichlet n b,b)) := by
  have hmem := (periodOneL1Inclusion.continuous.tendsto a).eventually
    (isOpen_hillHminusCanonicalDirichletDomain.mem_nhds ha)
  exact hmem.mono (fun b hb => hillHminusDirichletNorming_L1_eq n b hb)

theorem fderiv_hillHminusDirichletNorming_L1_family
    (n : ℕ+) (a : Coeff 1) (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) (h : Coeff 1) :
    (fderiv ℂ (hillHminusDirichletNorming n) (periodOneL1Inclusion a)) (periodOneL1Inclusion h)=
      (fderiv ℂ (fun b => hillL1TerminalFamily (hillL1CanonicalDirichlet n a,b)) a) h+
        deriv (fun z => hillL1TerminalFamily (z,a)) (hillL1CanonicalDirichlet n a)*
          (fderiv ℂ (hillHminusCanonicalDirichlet n) (periodOneL1Inclusion a)) (periodOneL1Inclusion h) :=
  NLS.FunctionalAnalysis.fderiv_linear_pullback_moving_spectral
    (hillHminusDirichletNorming n) (hillHminusCanonicalDirichlet n) hillL1TerminalFamily periodOneL1Inclusion a h
    (analyticOnNhd_hillHminusDirichletNorming n (periodOneL1Inclusion a) ha).differentiableAt
    (analyticOnNhd_hillHminusCanonicalDirichlet n (periodOneL1Inclusion a) ha).differentiableAt
    (analyticOnNhd_hillL1TerminalFamily (hillL1CanonicalDirichlet n a,a) (mem_univ _)).differentiableAt
    (hillHminusDirichletNorming_L1_eventually_eq_at n a ha)

end NLS.KdV
