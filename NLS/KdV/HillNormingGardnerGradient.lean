import NLS.KdV.HillNormingSourceDerivative

/-! The ACTUAL native norming H1 cotangent and its original Fourier
kernel at every Wiener source in the common complex domain. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.KdV

def hillHminusNormingGradient (n : ℕ+) (q : PeriodOneHminusOne) : WeightedCoeff (Weight.sobolev 1) 2 :=
  NLS.Poisson.hminusScalarGradient (hillHminusDirichletNorming n) q

theorem analyticOnNhd_hillHminusNormingGradient (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusNormingGradient n) hillHminusCanonicalDirichletDomain :=
  NLS.Poisson.analyticOnNhd_hminusScalarGradient _ (analyticOnNhd_hillHminusDirichletNorming n)

def hillWienerNormingRatio (n : ℕ+) (a : Coeff 1) : ℂ :=
  deriv (classicalHillDirichletTerminal (periodOneL1PotentialCurve a)) (hillL1CanonicalDirichlet n a)/
    deriv (hillHminusDirichlet (periodOneL1Inclusion a)) (hillL1CanonicalDirichlet n a)

def hillWienerNormingKernel (n : ℕ+) (a : Coeff 1) : ℝ → ℂ :=
  classicalHillNormingGradient (periodOneL1PotentialCurve a) (hillL1CanonicalDirichlet n a) (hillWienerNormingRatio n a)

def hillWienerNormingKernelPrime (n : ℕ+) (a : Coeff 1) : ℝ → ℂ :=
  classicalHillNormingGradientPrime (periodOneL1PotentialCurve a) (hillL1CanonicalDirichlet n a) (hillWienerNormingRatio n a)

theorem continuous_hillWienerNormingKernel (n : ℕ+) (a : Coeff 1) :
    Continuous (hillWienerNormingKernel n a) := continuous_classicalHillNormingGradient _ _ _

theorem continuous_hillWienerNormingKernelPrime (n : ℕ+) (a : Coeff 1) :
    Continuous (hillWienerNormingKernelPrime n a) := continuous_classicalHillNormingGradientPrime _ _ _

theorem hasDerivAt_hillWienerNormingKernel (n : ℕ+) (a : Coeff 1) (t : Icc (0:ℝ) 1) :
    HasDerivAt (hillWienerNormingKernel n a) (hillWienerNormingKernelPrime n a t) t :=
  hasDerivAt_classicalHillNormingGradient _ _ _ t

theorem hillWienerNormingKernel_actual_root (n : ℕ+) (a : Coeff 1)
    (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) :
    classicalHillS (periodOneL1PotentialCurve a) (hillL1CanonicalDirichlet n a) 1=0 := by
  change classicalHillDirichlet (periodOneL1PotentialCurve a) (hillL1CanonicalDirichlet n a)=0
  rw [← hillHminusDirichlet_eq_classical_L1]
  exact hillHminusCanonicalDirichlet_is_root n (periodOneL1Inclusion a) ha

theorem hillWienerNormingKernel_boundary (n : ℕ+) (a : Coeff 1)
    (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) :
    hillWienerNormingKernel n a 1=hillWienerNormingKernel n a 0 ∧
      hillWienerNormingKernelPrime n a 1=hillWienerNormingKernelPrime n a 0 := by
  obtain ⟨h0,h1,hp0,hp1⟩ := classicalHillNormingGradient_boundary_at_root
    (periodOneL1PotentialCurve a) (hillL1CanonicalDirichlet n a) (hillWienerNormingRatio n a)
      (hillWienerNormingKernel_actual_root n a ha)
  exact ⟨h1.trans h0.symm,hp1.trans hp0.symm⟩

theorem hillHminusNormingGradient_L1_coefficients (n : ℕ+) (a : Coeff 1)
    (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) (k : ℤ) :
    (hillHminusNormingGradient n (periodOneL1Inclusion a)).val k=
      unitFourierCoefficient (hillWienerNormingKernel n a) k := by
  rw [hillHminusNormingGradient,NLS.Poisson.hminusScalarGradient_apply,
    ← periodOneL1Inclusion_ofFinsupp,fderiv_hillHminusDirichletNorming_L1_integral n a ha]
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x hx
  have hxi : x ∈ Icc (0:ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
  change extend (periodOneL1PotentialCurve (Coeff.ofFinsupp (Finsupp.single (-k) 1))) x*
    hillWienerNormingKernel n a x=hillWienerNormingKernel n a x*wave (-(2*k)) x
  rw [extend_coe _ ⟨x,hxi⟩,periodOneL1PotentialCurve_apply,periodOneSynthesis_ofFinsupp]
  rw [show polynomial (Finsupp.single (-k) 1) x=wave (-(2*k)) x by simp [polynomial]]
  ring

end NLS.KdV
