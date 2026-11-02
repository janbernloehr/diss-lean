import NLS.ZakharovShabat.ClassicalNLSDirichletMotion
import NLS.ZakharovShabat.ContinuousSourceBoundaryGradient
import NLS.ZakharovShabat.ContinuousSourceAntiDiscriminantGradient
import NLS.ZakharovShabat.SourceBoundaryNormalizedRootVariation
import NLS.ZakharovShabat.SourceDirichletSignData

/-! Physical NLS velocity of the original indexed Dirichlet coordinates. -/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.LinearVolterra
open scoped ContDiff ComplexConjugate ENNReal
namespace NLS.ZakharovShabat

/-- The actual Hilbert source Dirichlet differential in the physical NLS
direction, at every signed index and every smooth periodic real source. -/
theorem sourceDirichletRoot_physicalNLS_differential
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (φ : realTypeSourceSubmodule 2) (h : CoeffPair 2) (Φ H : Curve (ℂ × ℂ))
    (hφ : physicalBase (periodOnePotential φ.val) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hh : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H)
    (hΦ : ∀ x : Icc (0 : ℝ) 1, Φ x = (a x,b x))
    (hH : ∀ x : Icc (0 : ℝ) 1,
      H x = ((classicalNLSVectorField a b).1 x,(classicalNLSVectorField a b).2 x))
    (n : ℤ) :
    (fderiv ℂ (fun ψ : CoeffPair 2 =>
        canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ n) φ.val) h =
      let z := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val n;
      -(sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ.val z *
          classicalNLSDirichletSpeedFactor a b z) /
        deriv (periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet φ.val) z := by
  dsimp only
  let z := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val n
  have hroot : classicalSeparatedCharacteristic .dirichlet Φ z = 0 := by
    rw [← periodOneBoundaryCharacteristic_eq_classical_of_continuous .dirichlet φ.val Φ hφ z]
    exact periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero (by simp) (by norm_num)
      .dirichlet φ.val n
  rw [fderiv_canonicalPeriodOneBoundaryRoot_eq_cotangent (by simp) (by norm_num)
    .dirichlet φ.val φ.property n]
  simp only [smul_apply,smul_eq_mul]
  rw [sourceBoundaryCharacteristicCotangent_continuous_direction .dirichlet φ.val h Φ H hφ hh,
    fderiv_classicalDirichletCharacteristic_physicalNLS_at_root a b ha hb hpa hpb
      Φ H hΦ hH z hroot,
    ← sourceAntiDiscriminantCandidate_eq_classical_of_continuous φ.val Φ hφ z]
  ring

/-- The real multiplier of the terminal sheet value in physical NLS
time. It includes the original characteristic derivative normalization. -/
def sourceNLSDirichletVelocityMultiplier (φ : realTypeSourceSubmodule 2)
    (a : ℝ → ℂ) (n : ℤ) : ℝ :=
  let z := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val n;
  -(2*z.re^2-2*z.re*(a 0).re+‖a 0‖^2+(deriv a 0).im) /
    (deriv (periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet φ.val) z).re

/-- On the real form, the actual indexed Dirichlet velocity is the
terminal anti-discriminant times its real physical NLS multiplier. -/
theorem sourceDirichletRoot_physicalNLS_real_differential
    (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hpa : Function.Periodic a 1)
    (φ : realTypeSourceSubmodule 2) (h : CoeffPair 2) (Φ H : Curve (ℂ × ℂ))
    (hφ : physicalBase (periodOnePotential φ.val) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hh : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H)
    (hΦ : ∀ x : Icc (0 : ℝ) 1, Φ x = (a x,conj (a x)))
    (hH : ∀ x : Icc (0 : ℝ) 1,
      H x = ((classicalNLSVectorField a (fun y => conj (a y))).1 x,
        (classicalNLSVectorField a (fun y => conj (a y))).2 x))
    (n : ℤ) :
    (fderiv ℂ (fun ψ : CoeffPair 2 =>
        canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ n) φ.val) h =
      ((sourceNLSDirichletVelocityMultiplier φ a n *
        (sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ.val
          (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val n)).re : ℝ) : ℂ) := by
  let z := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val n
  let S := sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ.val z
  let d := deriv (periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet φ.val) z
  have hz : (z.re : ℂ) = z := Complex.ext rfl (by
    simpa only [ofReal_im] using
      (canonicalPeriodOneBoundaryRoots_im_eq_zero (by simp) (by norm_num)
        .dirichlet φ.val φ.property n).symm)
  have hS : (S.re : ℂ) = S := Complex.ext rfl (by
    simpa only [ofReal_im] using
      (sourceDirichletTerminalAntiDiscriminant_im_eq_zero (by simp) (by norm_num) φ n).symm)
  have hd : (d.re : ℂ) = d := Complex.ext rfl (by
    simpa only [ofReal_im] using
      (deriv_periodOneBoundaryCharacteristic_at_root_im_eq_zero (by simp) (by norm_num)
        .dirichlet φ.val φ.property n).symm)
  have hfactor : classicalNLSDirichletSpeedFactor a (fun x => conj (a x)) z =
      ((2*z.re^2-2*z.re*(a 0).re+‖a 0‖^2+(deriv a 0).im : ℝ) : ℂ) := by
    nth_rw 1 [← hz]
    exact classicalNLSDirichletSpeedFactor_real a z.re
  rw [sourceDirichletRoot_physicalNLS_differential a (fun x => conj (a x)) ha (conjCLE.contDiff.comp ha)
    hpa (fun x => congrArg conj (hpa x)) φ h Φ H hφ hh hΦ hH n]
  change -(S*classicalNLSDirichletSpeedFactor a (fun x => conj (a x)) z)/d = _
  rw [hfactor,← hS,← hd]
  dsimp only [sourceNLSDirichletVelocityMultiplier]
  push_cast
  ring

/-- The source sheet sign enters the physical direction through the
proved real multiplier, with zero values included. -/
theorem sourceDirichletRoot_physicalNLS_velocity_sign
    (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hpa : Function.Periodic a 1)
    (φ : realTypeSourceSubmodule 2) (h : CoeffPair 2) (Φ H : Curve (ℂ × ℂ))
    (hφ : physicalBase (periodOnePotential φ.val) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hh : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H)
    (hΦ : ∀ x : Icc (0 : ℝ) 1, Φ x = (a x,conj (a x)))
    (hH : ∀ x : Icc (0 : ℝ) 1,
      H x = ((classicalNLSVectorField a (fun y => conj (a y))).1 x,
        (classicalNLSVectorField a (fun y => conj (a y))).2 x))
    (n : ℤ) :
    SignType.sign ((fderiv ℂ (fun ψ : CoeffPair 2 =>
        canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ n) φ.val) h).re =
      sourceDirichletSign (by simp) (by norm_num) φ n *
        SignType.sign (sourceNLSDirichletVelocityMultiplier φ a n) := by
  rw [sourceDirichletRoot_physicalNLS_real_differential a ha hpa φ h Φ H hφ hh hΦ hH n,
    ofReal_re,sign_mul,mul_comm]
  rfl

/-- A source trajectory with the genuine physical NLS tangent has the
same actual indexed Dirichlet velocity in real time. -/
theorem hasDerivAt_sourceDirichletRoot_physicalNLS
    (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hpa : Function.Periodic a 1)
    (φ : realTypeSourceSubmodule 2) (h : CoeffPair 2) (Φ H : Curve (ℂ × ℂ))
    (hφ : physicalBase (periodOnePotential φ.val) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hh : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H)
    (hΦ : ∀ x : Icc (0 : ℝ) 1, Φ x = (a x,conj (a x)))
    (hH : ∀ x : Icc (0 : ℝ) 1,
      H x = ((classicalNLSVectorField a (fun y => conj (a y))).1 x,
        (classicalNLSVectorField a (fun y => conj (a y))).2 x))
    (γ : ℝ → CoeffPair 2) (time : ℝ) (hγ : HasDerivAt γ h time)
    (hbase : γ time = φ.val) (n : ℤ) :
    HasDerivAt (fun t => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet (γ t) n)
      ((sourceNLSDirichletVelocityMultiplier φ a n *
        (sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ.val
          (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val n)).re : ℝ) : ℂ)
      time := by
  have hμ := (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType (by simp) (by norm_num)
    .dirichlet φ.val φ.property n).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have ht := hμ.comp_hasDerivAt_of_eq time hγ hbase.symm
  change HasDerivAt (fun t => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet (γ t) n)
    ((fderiv ℂ (fun ψ : CoeffPair 2 =>
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ n) φ.val) h) time at ht
  rw [sourceDirichletRoot_physicalNLS_real_differential a ha hpa φ h Φ H hφ hh hΦ hH n] at ht
  exact ht

end NLS.ZakharovShabat
