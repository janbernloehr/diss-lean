import NLS.MKdV.DiagonalDiscriminantGradient
import NLS.MKdV.SobolevMiuraPrimitive
import NLS.ZakharovShabat.ContinuousSourceDiscriminantGradient

/-! # The exact discriminant cotangent recurrence on complex H1 diagonals

Physical Fourier realization identifies both full source cotangents.
The gradient differential equation then gives the period-one recurrence
at every integer Fourier mode, including zero, without smoothness or
spectral cut assumptions.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.MKdV

theorem physicalBase_miuraDiagonal (a : ScalarDomain 2) :
    physicalBase (periodOnePotential (sobolevSourceInclusion (a,a))) =ᵐ[volume.restrict (Ioc 0 1)]
      extend (miuraDiagonalCurveCLM (periodOneMiuraCurve a)) := by
  let c : Domain 2 := (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a)
  have he : periodOnePotential (sobolevSourceInclusion (a,a)) = domainInclusion c := by
    apply Prod.ext <;> ext n <;>
      simp [periodOnePotential_apply,domainInclusion_apply,c,scalarInclusion_apply,
        Coeff.periodDoubleSobolev_apply,sobolevSourceInclusion]
  rw [he]
  exact physicalBase_eq_extend_physicalDomainCurve c

theorem miuraDiscriminantCotangent_fourier (a : ScalarDomain 2) (z : ℂ) (m : ℤ) :
    (2*I*(Real.pi : ℂ)*m) *
        ((CoeffPair.cotangentCoefficients le_rfl (sourceDiscriminantCotangent (by simp) z
          (sobolevSourceInclusion (a,a)))).1 (-m) +
         (CoeffPair.cotangentCoefficients le_rfl (sourceDiscriminantCotangent (by simp) z
          (sobolevSourceInclusion (a,a)))).2 (-m)) =
      2*I*z*((CoeffPair.cotangentCoefficients le_rfl (sourceDiscriminantCotangent (by simp) z
          (sobolevSourceInclusion (a,a)))).1 (-m) -
         (CoeffPair.cotangentCoefficients le_rfl (sourceDiscriminantCotangent (by simp) z
          (sobolevSourceInclusion (a,a)))).2 (-m)) := by
  let Φ := miuraDiagonalCurveCLM (periodOneMiuraCurve a)
  rw [cotangentCoefficients_sourceDiscriminant_continuous_fst _ Φ (physicalBase_miuraDiagonal a),
    cotangentCoefficients_sourceDiscriminant_continuous_snd _ Φ (physicalBase_miuraDiagonal a),neg_neg]
  have hc := continuous_classicalDiscriminantGradient Φ z
  have hi₁ : IntervalIntegrable (fun s => (classicalDiscriminantGradient Φ z s).1*wave (-(2*m)) s) volume 0 1 :=
    (hc.fst.mul (continuous_wave _)).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun s => (classicalDiscriminantGradient Φ z s).2*wave (-(2*m)) s) volume 0 1 :=
    (hc.snd.mul (continuous_wave _)).intervalIntegrable 0 1
  have h := diagonalDiscriminantGradient_fourier Φ (fun _ => rfl) z m
  simpa only [unitFourierCoefficient,add_mul,sub_mul,intervalIntegral.integral_add hi₁ hi₂,
    intervalIntegral.integral_sub hi₁ hi₂] using h

end NLS.MKdV
