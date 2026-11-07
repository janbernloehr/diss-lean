import NLS.KdV.HillNormingGardnerGradient
import NLS.KdV.ClassicalHillNormingCommutation
import NLS.KdV.HminusOneCanonicalDirichletMultiplicity
import NLS.Poisson.GardnerIntegralCoefficients

/-! Actual multiplier/multiplier Gardner commutation on the entire
unchanged common complex Dirichlet domain. The actual moving gradients
transfer from their Wiener kernels by verified source density. -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ENNReal
namespace NLS.KdV

theorem hillHminusNormingGardnerBracket_L1_eq_integral (n m : ℕ+) (a : Coeff 1)
    (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusDirichletNorming n) (hillHminusDirichletNorming m)
      (periodOneL1Inclusion a)=
      ∫ x in (0:ℝ)..1, hillWienerNormingKernel n a x*hillWienerNormingKernelPrime m a x :=
  NLS.Poisson.gardnerBivector_eq_integral_of_coefficients
    (hillHminusNormingGradient n (periodOneL1Inclusion a)) (hillHminusNormingGradient m (periodOneL1Inclusion a))
    (hillWienerNormingKernel n a) (hillWienerNormingKernel m a) (hillWienerNormingKernelPrime m a)
    (continuous_hillWienerNormingKernel n a) (continuous_hillWienerNormingKernel m a)
    (continuous_hillWienerNormingKernelPrime m a)
    (fun t ht => hasDerivAt_hillWienerNormingKernel m a ⟨t,ht.1.le,ht.2.le⟩)
    (hillWienerNormingKernel_boundary m a ha).1
    (hillHminusNormingGradient_L1_coefficients n a ha) (hillHminusNormingGradient_L1_coefficients m a ha)

theorem hillHminusNormings_Gardner_commute_L1 (n m : ℕ+) (a : Coeff 1)
    (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusDirichletNorming n) (hillHminusDirichletNorming m)
      (periodOneL1Inclusion a)=0 := by
  by_cases hnm : n=m
  · subst m
    exact NLS.Poisson.hminusGardnerBracket_self _ _
  · rw [hillHminusNormingGardnerBracket_L1_eq_integral n m a ha]
    exact integral_classicalHillNormingGradients_eq_zero (periodOneL1PotentialCurve a)
      (hillL1CanonicalDirichlet n a) (hillL1CanonicalDirichlet m a)
      (hillWienerNormingRatio n a) (hillWienerNormingRatio m a)
      (hillWienerNormingKernel_actual_root n a ha) (hillWienerNormingKernel_actual_root m a ha)
      (fun he => hnm (injective_hillHminusCanonicalDirichlet (periodOneL1Inclusion a) ha he))

theorem hillHminusNormings_Gardner_commute (n m : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusDirichletNorming n) (hillHminusDirichletNorming m) q=0 := by
  have hB : AnalyticOnNhd ℂ
      (NLS.Poisson.hminusGardnerBracket (hillHminusDirichletNorming n) (hillHminusDirichletNorming m))
      hillHminusCanonicalDirichletDomain :=
    NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
      (analyticOnNhd_hillHminusDirichletNorming n) (analyticOnNhd_hillHminusDirichletNorming m)
  have he : EqOn (NLS.Poisson.hminusGardnerBracket (hillHminusDirichletNorming n) (hillHminusDirichletNorming m))
      (fun _ => 0) (hillHminusCanonicalDirichletDomain ∩ range periodOneL1Inclusion) := by
    rintro _ ⟨ha,a,rfl⟩
    exact hillHminusNormings_Gardner_commute_L1 n m a ha
  exact he.of_subset_closure hB.continuousOn continuousOn_const inter_subset_left
    (fun p hp => isOpen_hillHminusCanonicalDirichletDomain.inter_closure ⟨hp,denseRange_periodOneL1Inclusion p⟩) hq

end NLS.KdV
