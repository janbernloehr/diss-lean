import NLS.Fourier.FourierNLSSpatialDerivatives
import NLS.Fourier.FourierNLSPhysicalSynthesis
import NLS.ZakharovShabat.ClassicalNLSDifferenceEstimate

/-! # The strong physical time equation

A continuous order-two lift makes the original Fourier velocity continuous
in ℓ¹. Coordinate integration supplies its strong derivative, and bounded
synthesis gives the time derivative in the uniform physical norm.
-/
noncomputable section
open Set Complex
namespace NLS.Fourier

/-- The original (not interaction) Fourier velocity from an order-two lift. -/
def nlsStrongVelocity
    (v : ℝ → WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1)
    (z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1) (time : ℝ) :=
  nlsLinearCLM (v time) + cubicNLS SpectralWeight.one (z time)

/-- The original curve has a strong ℓ¹ derivative, including within endpoints. -/
theorem IsFourierNLSTrajectoryOn.hasDerivWithinAt_original
    {a b : ℝ} {z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1}
    (hz : IsFourierNLSTrajectoryOn SpectralWeight.one a b z)
    (v : ℝ → WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1)
    (hv : ContinuousOn v (Icc a b))
    (he : ∀ time ∈ Icc a b, ∀ n : ℤ, (v time).val n = (z time).val n)
    (time : ℝ) (ht : time ∈ Icc a b) :
    HasDerivWithinAt z (nlsStrongVelocity v z time) (Icc a b) time := by
  have hg : ContinuousOn (nlsStrongVelocity v z) (Icc a b) :=
    (nlsLinearCLM.continuous.comp_continuousOn hv).add
      ((continuous_cubicNLS SpectralWeight.one).comp_continuousOn hz.continuous)
  apply SpectralWeight.one.hasDerivWithinAt_of_coordinate_derivatives a b z _ hz.continuous hg _ time ht
  intro r hr n
  have hd := (hz.equation r ⟨hr.1.le,hr.2.le⟩ n).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  simpa only [nlsStrongVelocity,WeightedCoeff.add_val,Pi.add_apply,nlsLinearCLM_apply,
    he r ⟨hr.1.le,hr.2.le⟩ n] using hd

/-- The synthesized original velocity agrees with the classical NLS expression. -/
theorem nlsStrongVelocity_physical
    {a b : ℝ} (v : ℝ → WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1)
    (z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1)
    (he : ∀ time ∈ Icc a b, ∀ n : ℤ, (v time).val n = (z time).val n)
    (time : ℝ) (ht : time ∈ Icc a b) (x : ℝ) :
    periodOneSynthesis (SpectralWeight.one.toCoeff (nlsStrongVelocity v z time)) x =
      NLS.ZakharovShabat.scalarClassicalNLSVectorField
        (fun y : ℝ => fourierNLSPhysicalCurve SpectralWeight.one z time (y : AddCircle (2 : ℝ))) x := by
  have heq : (SpectralWeight.sobolev 2 (by norm_num)).toCoeff (v time) =
      SpectralWeight.one.toCoeff (z time) := by
    ext n
    simpa only [SpectralWeight.toCoeff_apply] using he time ht n
  simp only [nlsStrongVelocity,map_add,periodOneSynthesis_add,
    periodOneSynthesis_nlsLinearCLM,heq,periodOneSynthesis_cubicNLS,
    fourierNLSPhysicalCurve_apply,NLS.ZakharovShabat.scalarClassicalNLSVectorField,
    NLS.ZakharovShabat.classicalNLSCubic]
  ring

/-- Strong time differentiation in the uniform physical norm, with the literal PDE. -/
theorem IsFourierNLSTrajectoryOn.hasDerivWithinAt_physical
    {a b : ℝ} {z : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1}
    (hz : IsFourierNLSTrajectoryOn SpectralWeight.one a b z)
    (v : ℝ → WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1)
    (hv : ContinuousOn v (Icc a b))
    (he : ∀ time ∈ Icc a b, ∀ n : ℤ, (v time).val n = (z time).val n)
    (time : ℝ) (ht : time ∈ Icc a b) :
    ∃ velocity : C(AddCircle (2 : ℝ), ℂ),
      HasDerivWithinAt (fourierNLSPhysicalCurve SpectralWeight.one z) velocity (Icc a b) time ∧
      ∀ x : ℝ, velocity (x : AddCircle (2 : ℝ)) =
        NLS.ZakharovShabat.scalarClassicalNLSVectorField
          (fun y : ℝ => fourierNLSPhysicalCurve SpectralWeight.one z time (y : AddCircle (2 : ℝ))) x := by
  let L := (periodOneSynthesisCLM.comp SpectralWeight.one.toCoeff).restrictScalars ℝ
  refine ⟨L (nlsStrongVelocity v z time),?_,?_⟩
  · exact L.hasFDerivAt.comp_hasDerivWithinAt time (hz.hasDerivWithinAt_original v hv he time ht)
  · intro x
    exact nlsStrongVelocity_physical v z he time ht x

end NLS.Fourier
