import NLS.KdV.SingularDirichletMiuraConverse
import NLS.KdV.SingularDirichletMiuraRegularity
import NLS.Fourier.UnitIntervalFourierLinear

/-! # The physical quasi-Hill rows imply the entire native Dirichlet equation

The quasi-derivative can have arbitrary endpoint jump. Integration by parts
retains that jump, and full H1 duality promotes every Fourier coefficient
to the complete native zero-trace weak equation.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat

/-- The independent physical rows give a native eigenvector, with no
periodicity or additional boundary trace imposed on the quasi-derivative. -/
theorem singularDirichletMiura_eigen_of_physical_rows (u : Coeff 2) (lambda : ℂ)
    (f : UnitDirichletH1) (G : ℝ → ℂ) (hGc : Continuous G)
    (hGa : AbsolutelyContinuousOnInterval G 0 1)
    (hGr : MemLp (deriv G) 2 (volume.restrict (Ioc 0 1)))
    (hYd : ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt (unitDirichletRepresentative f)
      (unitL2SynthesisEquiv u x*unitDirichletRepresentative f x+G x) x)
    (hGd : ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt G
      (-lambda*unitDirichletRepresentative f x-unitL2SynthesisEquiv u x*G x) x) :
    singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f =
      lambda • singularDirichletDomainInclusion f := by
  let Y := unitDirichletRepresentative f
  have hQG : unitL2SynthesisEquiv (unitDirichletQuasiDerivative u f)
      =ᵐ[volume.restrict (Ioc 0 1)] G := by
    filter_upwards [unitDirichletQuasiDerivative_representative u f, hYd] with x hq hy
    rw [hy.deriv] at hq
    simpa only [add_sub_cancel_left] using hq
  have hQcoef (n : ℤ) : unitFourierCoefficient G n = unitDirichletQuasiDerivative u f n := by
    rw [← unitFourierCoefficient_congr_ae hQG, unitFourierCoefficient_unitL2Synthesis]
  have hYcoef (n : ℤ) : unitFourierCoefficient Y n = f.val.val n := by
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    exact periodOneCoefficient_periodOneSobolevSynthesis f.val n
  have hYi : IntervalIntegrable Y volume 0 1 :=
    (continuous_periodOneSobolevSynthesis f.val).intervalIntegrable 0 1
  have hGm := memLp_two_interval hGc 0 1 (by norm_num)
  have hUGi : IntervalIntegrable (fun x => unitL2SynthesisEquiv u x*G x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((Lp.memLp (unitL2SynthesisEquiv u)).integrable_mul hGm)
  have hGi : IntervalIntegrable (deriv G) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hGr.integrable (by norm_num))
  have hder : deriv G =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => -lambda*Y x-unitL2SynthesisEquiv u x*G x) := by
    filter_upwards [hGd] with x hx
    exact hx.deriv
  apply singularDirichletMiura_eigen_of_weak_equation u lambda (G 1-G 0) f
  intro n
  have hcoef := unitFourierCoefficient_congr_ae hder n
  rw [unitFourierCoefficient_deriv_of_ac hGa hGi,
    unitFourierCoefficient_sub _ _ (hYi.const_mul (-lambda)) hUGi,
    unitFourierCoefficient_const_mul, unitFourierCoefficient_L2_product _ _
      (Lp.memLp (unitL2SynthesisEquiv u)) hGm] at hcoef
  simp only [hQcoef, hYcoef, unitFourierCoefficient_unitL2Synthesis] at hcoef
  linear_combination hcoef

end NLS.KdV
