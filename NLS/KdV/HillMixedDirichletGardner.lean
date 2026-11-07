import NLS.KdV.ClassicalHillMixedGradientBracket
import NLS.KdV.HillCanonicalDirichletGardner
import NLS.KdV.HillDiscriminantGardnerGradient
import NLS.KdV.HminusOneDirichletSheet

/-! The actual discriminant/Dirichlet-eigenvalue Gardner identity.
The prescribed sheet sign and exact factor two are retained. Its
undivided form covers equal energies and closed periodic gaps. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem hillHminus_mixed_Gardner_L1 (a : Coeff 1) (μ ν : ℂ) :
    2*(μ-ν)*NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ)
      (fun p => hillHminusDirichlet p ν) (periodOneL1Inclusion a)=
      classicalHillS (periodOneL1PotentialCurve a) ν 1*
        (classicalHillSPrime (periodOneL1PotentialCurve a) μ 1-classicalHillC (periodOneL1PotentialCurve a) μ 1)-
      classicalHillS (periodOneL1PotentialCurve a) μ 1*
        (classicalHillSPrime (periodOneL1PotentialCurve a) ν 1-classicalHillC (periodOneL1PotentialCurve a) ν 1) := by
  have hi := NLS.Poisson.gardnerBivector_eq_integral_of_coefficients
    (hillHminusDiscriminantGradient μ (periodOneL1Inclusion a))
    (hillHminusDirichletGradient ν (periodOneL1Inclusion a))
    (classicalHillTraceGradient (periodOneL1PotentialCurve a) μ)
    (classicalHillDirichletGradient (periodOneL1PotentialCurve a) ν)
    (classicalHillDirichletGradientPrime (periodOneL1PotentialCurve a) ν)
    (continuous_classicalHillTraceGradient (periodOneL1PotentialCurve a) μ)
    (continuous_classicalHillDirichletGradient (periodOneL1PotentialCurve a) ν)
    (continuous_classicalHillDirichletGradientPrime (periodOneL1PotentialCurve a) ν)
    (fun t ht => hasDerivAt_classicalHillDirichletGradient (periodOneL1PotentialCurve a) ν ⟨t,ht.1.le,ht.2.le⟩)
    (classicalHillDirichletGradient_boundary (periodOneL1PotentialCurve a) ν)
    (hillHminusDiscriminantGradient_L1_coefficients μ a) (hillHminusDirichletGradient_L1_coefficients ν a)
  change NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ)
    (fun p => hillHminusDirichlet p ν) (periodOneL1Inclusion a)=_ at hi
  rw [hi]
  exact classicalHill_mixed_gradient_bracket _ μ ν

theorem hillHminus_discriminant_Dirichlet_Gardner_L1
    (n : ℕ+) (a : Coeff 1) (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) (μ : ℂ) :
    2*(μ-hillHminusCanonicalDirichlet n (periodOneL1Inclusion a))*
      deriv (hillHminusDirichlet (periodOneL1Inclusion a)) (hillHminusCanonicalDirichlet n (periodOneL1Inclusion a))*
      NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalDirichlet n)
        (periodOneL1Inclusion a)=
      -hillHminusDirichlet (periodOneL1Inclusion a) μ*hillHminusDirichletSheet n (periodOneL1Inclusion a) := by
  let q := periodOneL1Inclusion a
  let Q := periodOneL1PotentialCurve a
  let ν := hillHminusCanonicalDirichlet n q
  let d := deriv (hillHminusDirichlet q) ν
  have hroot : classicalHillS Q ν 1=0 := by
    change classicalHillDirichlet Q ν=0
    rw [← hillHminusDirichlet_eq_classical_L1]
    exact hillHminusCanonicalDirichlet_is_root n q ha
  have hnorm : hillHminusDirichletNorming n q=classicalHillSPrime Q ν 1 :=
    hillHminusDirichletNorming_eq_classical_L1 n a ha
  have hdet := classicalHillFundamentalColumns_det Q ν ⟨1,by constructor <;> norm_num⟩
  rw [hroot,mul_zero,sub_zero] at hdet
  have hnz : classicalHillSPrime Q ν 1 ≠ 0 := by
    rw [← hnorm]
    exact hillHminusDirichletNorming_ne_zero n q ha
  have hA : classicalHillC Q ν 1=(classicalHillSPrime Q ν 1)⁻¹ := by
    apply mul_right_cancel₀ hnz
    rw [inv_mul_cancel₀ hnz]
    exact hdet
  have hsheet : hillHminusDirichletSheet n q=classicalHillC Q ν 1-classicalHillSPrime Q ν 1 := by
    rw [hillHminusDirichletSheet,hnorm,← hA]
  have hb := congrArg
    (fun M : PeriodOneHminusOne →L[ℂ] ℂ => NLS.Poisson.gardnerCotangentBivector
      (fderiv ℂ (fun p => hillHminusDiscriminant p μ) q) M)
    (fderiv_hillHminusCanonicalDirichlet_eq_characteristic n q ha)
  simp only [map_smul,smul_eq_mul] at hb
  change NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalDirichlet n) q=
    -(d⁻¹)*NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (fun p => hillHminusDirichlet p ν) q at hb
  have hd : d ≠ 0 := deriv_hillHminusCanonicalDirichlet_ne_zero n q ha
  have hbal : d*NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalDirichlet n) q=
      -NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (fun p => hillHminusDirichlet p ν) q := by
    rw [hb]
    field_simp
  have hi := hillHminus_mixed_Gardner_L1 a μ ν
  change 2*(μ-ν)*NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (fun p => hillHminusDirichlet p ν) q=_ at hi
  rw [hroot,zero_mul,zero_sub] at hi
  change 2*(μ-ν)*d*NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalDirichlet n) q=
    -hillHminusDirichlet q μ*hillHminusDirichletSheet n q
  rw [hsheet,hillHminusDirichlet_eq_classical_L1]
  change 2*(μ-ν)*d*NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalDirichlet n) q=
    -classicalHillS Q μ 1*(classicalHillC Q ν 1-classicalHillSPrime Q ν 1)
  linear_combination (2*(μ-ν))*hbal-hi

theorem hillHminus_discriminant_Dirichlet_Gardner
    (n : ℕ+) (μ : ℂ) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    2*(μ-hillHminusCanonicalDirichlet n q)*
      deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q)*
      NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalDirichlet n) q=
      -hillHminusDirichlet q μ*hillHminusDirichletSheet n q := by
  let U := hillHminusCanonicalDirichletDomain
  let f : PeriodOneHminusOne → ℂ := fun p => 2*(μ-hillHminusCanonicalDirichlet n p)*
    deriv (hillHminusDirichlet p) (hillHminusCanonicalDirichlet n p)*
      NLS.Poisson.hminusGardnerBracket (fun b => hillHminusDiscriminant b μ) (hillHminusCanonicalDirichlet n) p
  let g : PeriodOneHminusOne → ℂ := fun p => -hillHminusDirichlet p μ*hillHminusDirichletSheet n p
  let D : ℂ × PeriodOneHminusOne → ℂ := fun t => hillHminusDirichlet t.2 t.1
  have hE : Continuous (fun t : ℂ × PeriodOneHminusOne => deriv (hillHminusDirichlet t.2) t.1) :=
    continuousOn_univ.mp (continuousOn_spectral_deriv_of_analyticOnNhd D univ isOpen_univ
      analyticOnNhd_hillHminusDirichlet_joint)
  have hLabel : ContinuousOn (hillHminusCanonicalDirichlet n) U :=
    (analyticOnNhd_hillHminusCanonicalDirichlet n).continuousOn
  have hpair : ContinuousOn (fun p : PeriodOneHminusOne => (hillHminusCanonicalDirichlet n p,p)) U :=
    hLabel.prodMk (continuousOn_id : ContinuousOn (fun p : PeriodOneHminusOne => p) U)
  have hcomp := hE.comp_continuousOn hpair
  have hd : ContinuousOn (fun p : PeriodOneHminusOne => deriv (hillHminusDirichlet p) (hillHminusCanonicalDirichlet n p)) U := by
    simpa only [Function.comp_def] using hcomp
  have hNative : AnalyticOnNhd ℂ (fun p : PeriodOneHminusOne => hillHminusDiscriminant p μ) U :=
    (analyticOnNhd_hillHminusDiscriminant_source μ).mono (subset_univ U)
  have hCoord : AnalyticOnNhd ℂ (hillHminusCanonicalDirichlet n) U :=
    analyticOnNhd_hillHminusCanonicalDirichlet n
  have hB : ContinuousOn
      (fun p => NLS.Poisson.hminusGardnerBracket (fun b => hillHminusDiscriminant b μ) (hillHminusCanonicalDirichlet n) p) U :=
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket
      (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalDirichlet n) hNative hCoord).continuousOn
  have hf : ContinuousOn f U := ((continuousOn_const.mul (continuousOn_const.sub hLabel)).mul hd).mul hB
  have hg : ContinuousOn g U := (analyticOnNhd_hillHminusDirichlet_source μ).continuous.continuousOn.neg.mul
    (analyticOnNhd_hillHminusDirichletSheet n).continuousOn
  have he : EqOn f g (U ∩ range periodOneL1Inclusion) := by
    rintro _ ⟨ha,a,rfl⟩
    exact hillHminus_discriminant_Dirichlet_Gardner_L1 n a ha μ
  exact he.of_subset_closure hf hg inter_subset_left
    (fun p hp => isOpen_hillHminusCanonicalDirichletDomain.inter_closure ⟨hp,denseRange_periodOneL1Inclusion p⟩) hq

end NLS.KdV
