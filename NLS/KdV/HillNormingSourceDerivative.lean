import NLS.KdV.HillNativeNormingFirstVariation
import NLS.KdV.HillCanonicalDirichletGardner
import NLS.KdV.ClassicalHillNormingGradient
import NLS.KdV.HillNormingLocalComparison

/-! The actual full native moving norming derivative on EVERY Wiener
source in the common domain. Both the fixed-potential terminal variation
and the actual moving simple-root derivative are retained. -/
noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra NLS.Fourier NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem fderiv_hillL1TerminalFamily_source (μ : ℂ) (a : Coeff 1) :
    fderiv ℂ (fun b => hillL1TerminalFamily (μ,b)) a=
      (fderiv ℂ (fun Q => classicalHillDirichletTerminal Q μ) (periodOneL1PotentialCurve a)).comp
        periodOneL1PotentialCurve := by
  have he : (fun b => hillL1TerminalFamily (μ,b))=
      (fun b => classicalHillDirichletTerminal (periodOneL1PotentialCurve b) μ) :=
    funext (hillL1TerminalFamily_eq_classical μ)
  rw [he]
  let t : Icc (0:ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hP : DifferentiableAt ℂ (fun Q : Curve ℂ => classicalHillDirichletTerminal Q μ) (periodOneL1PotentialCurve a) :=
    (analyticAt_snd.comp (analyticOnNhd_classicalHillFlow_potential μ (0,1) t (periodOneL1PotentialCurve a) (mem_univ _))).differentiableAt
  exact (hP.hasFDerivAt.comp a periodOneL1PotentialCurve.hasFDerivAt).fderiv

theorem fderiv_hillHminusDirichletNorming_potential_L1
    (n : ℕ+) (a : Coeff 1) (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) (h : Coeff 1) :
    (fderiv ℂ (hillHminusDirichletNorming n) (periodOneL1Inclusion a)) (periodOneL1Inclusion h)=
      (fderiv ℂ (fun Q => classicalHillDirichletTerminal Q (hillL1CanonicalDirichlet n a))
        (periodOneL1PotentialCurve a)) (periodOneL1PotentialCurve h)+
      deriv (classicalHillDirichletTerminal (periodOneL1PotentialCurve a)) (hillL1CanonicalDirichlet n a)*
        (fderiv ℂ (hillHminusCanonicalDirichlet n) (periodOneL1Inclusion a)) (periodOneL1Inclusion h) := by
  have hm := fderiv_hillHminusDirichletNorming_L1_family n a ha h
  have hE : (fun z => hillL1TerminalFamily (z,a))=classicalHillDirichletTerminal (periodOneL1PotentialCurve a) :=
    funext (fun z => hillL1TerminalFamily_eq_classical z a)
  have hsource := congrArg (fun M : Coeff 1 →L[ℂ] ℂ => M h)
    (fderiv_hillL1TerminalFamily_source (hillL1CanonicalDirichlet n a) a)
  have henergy := congrArg (fun f : ℂ → ℂ => deriv f (hillL1CanonicalDirichlet n a)) hE
  calc
    _ = (fderiv ℂ (fun b => hillL1TerminalFamily (hillL1CanonicalDirichlet n a,b)) a) h+
        deriv (fun z => hillL1TerminalFamily (z,a)) (hillL1CanonicalDirichlet n a)*
          (fderiv ℂ (hillHminusCanonicalDirichlet n) (periodOneL1Inclusion a)) (periodOneL1Inclusion h) := hm
    _ = _ := congrArg₂ (fun x y : ℂ => x+y) hsource
      (congrArg (fun x : ℂ => x*(fderiv ℂ (hillHminusCanonicalDirichlet n) (periodOneL1Inclusion a))
        (periodOneL1Inclusion h)) henergy)


theorem fderiv_hillHminusDirichletNorming_L1_integral
    (n : ℕ+) (a : Coeff 1) (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) (h : Coeff 1) :
    (fderiv ℂ (hillHminusDirichletNorming n) (periodOneL1Inclusion a)) (periodOneL1Inclusion h)=
      ∫ x in (0:ℝ)..1, extend (periodOneL1PotentialCurve h) x*
        classicalHillNormingGradient (periodOneL1PotentialCurve a) (hillL1CanonicalDirichlet n a)
          (deriv (classicalHillDirichletTerminal (periodOneL1PotentialCurve a)) (hillL1CanonicalDirichlet n a)/
            deriv (hillHminusDirichlet (periodOneL1Inclusion a)) (hillL1CanonicalDirichlet n a)) x := by
  rw [fderiv_hillHminusDirichletNorming_potential_L1 n a ha h,
    fderiv_hillHminusCanonicalDirichlet_eq_characteristic n (periodOneL1Inclusion a) ha]
  simp only [smul_apply,smul_eq_mul]
  rw [fderiv_hillHminusDirichlet_potential_L1]
  have hi := classicalHillTerminal_sub_characteristic_derivative (periodOneL1PotentialCurve a) (periodOneL1PotentialCurve h)
    (hillL1CanonicalDirichlet n a)
    (deriv (classicalHillDirichletTerminal (periodOneL1PotentialCurve a)) (hillL1CanonicalDirichlet n a)/
      deriv (hillHminusDirichlet (periodOneL1Inclusion a)) (hillL1CanonicalDirichlet n a))
  rw [← hi]
  dsimp only [hillL1CanonicalDirichlet]
  ring

end NLS.KdV
