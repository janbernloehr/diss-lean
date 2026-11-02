import NLS.ZakharovShabat.SmoothNLSSourceDerivative
import NLS.ZakharovShabat.SourceNLSDirichletVelocity
import NLS.ZakharovShabat.SourceAbelStripCharacterization

/-! Actual indexed Dirichlet velocities along classical physical NLS solutions. -/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ComplexConjugate ENNReal
namespace NLS.ZakharovShabat

/-- The bounded Fourier source map reconstructs the given physical pair
almost everywhere on the original unit interval. -/
theorem physicalNLSSourceCLM_representative (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    physicalBase (periodOnePotential (physicalNLSSourceCLM f))
      =ᵐ[volume.restrict (Ioc 0 1)]
        (fun x : ℝ => (f (x : AddCircle (2 : ℝ)),conj (f (x : AddCircle (2 : ℝ))))) := by
  have hc : Continuous (fun x : ℝ => f (x : AddCircle (2 : ℝ))) :=
    f.continuous.comp (AddCircle.continuous_mk' (2 : ℝ))
  apply (sourcePhysicalL2_representative (physicalNLSSourceCLM f)).symm.trans
  apply sourcePhysicalL2_representative_of_coefficients _ _ _ hc (conjCLE.continuous.comp hc)
  · intro n
    rw [physicalNLSSourceCLM_fst,physicalNLSUnitFourierCLM_apply f hf]
  · intro n
    rw [physicalNLSSourceCLM_snd,physicalNLSUnitFourierCLM_apply f hf]
    simp only [periodOneCoefficient,← intervalFourierCoefficient_eq_fourierCoeffOn
      (by norm_num : (0 : ℝ) < 1)]
    exact intervalFourierCoefficient_conj _ n

/-- The reconstructed physical pair agrees with its continuous restriction,
so the existing classical source differential applies without a new premise. -/
theorem physicalNLSSourceCLM_eq_extend (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    physicalBase (periodOnePotential (physicalNLSSourceCLM f))
      =ᵐ[volume.restrict (Ioc 0 1)] extend
        (classicalPotentialOfFunctions
          (fun x : ℝ => f (x : AddCircle (2 : ℝ)))
          (fun x : ℝ => conj (f (x : AddCircle (2 : ℝ))))
          (f.continuous.comp (AddCircle.continuous_mk' (2 : ℝ)))
          (conjCLE.continuous.comp (f.continuous.comp (AddCircle.continuous_mk' (2 : ℝ))))) := by
  filter_upwards [physicalNLSSourceCLM_representative f hf,ae_restrict_mem measurableSet_Ioc]
    with x hx hmem
  rw [hx]
  change (f (x : AddCircle (2 : ℝ)),conj (f (x : AddCircle (2 : ℝ)))) =
    NLS.LinearVolterra.extend _ ((⟨x,hmem.1.le,hmem.2⟩ : Icc (0 : ℝ) 1) : ℝ)
  rw [extend_coe]
  rfl

/-- Every classical physical NLS trajectory has the original indexed
Dirichlet velocity with the exact characteristic and sheet normalization.
Both the Hilbert tangent and its physical representative follow from the PDE. -/
theorem IsClassicalNLSTrajectory.hasDerivAt_dirichletRoot
    {u : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u)
    (time : ℝ) (n : ℤ) :
    let φ := fun t => smoothPeriodOneSourceAt 2 (u t) (hu.spatial_smooth t) (hu.periodic t)
    let a := fun x : ℝ => u time (x : AddCircle (2 : ℝ))
    HasDerivAt (fun t => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num)
        .dirichlet (φ t).val n)
      ((sourceNLSDirichletVelocityMultiplier (φ time) a n *
        (sourceAntiDiscriminantCandidate (by simp) (by norm_num) (φ time).val
          (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet (φ time).val n)).re : ℝ) : ℂ)
      time := by
  dsimp only
  let a := fun x : ℝ => u time (x : AddCircle (2 : ℝ))
  let v := fun x : ℝ => deriv u time (x : AddCircle (2 : ℝ))
  have ha : Continuous a := (hu.spatial_smooth time).continuous
  have hv : Continuous v := (deriv u time).continuous.comp (AddCircle.continuous_mk' (2 : ℝ))
  let Φ := classicalPotentialOfFunctions a (fun x => conj (a x)) ha (conjCLE.continuous.comp ha)
  let H := classicalPotentialOfFunctions v (fun x => conj (v x)) hv (conjCLE.continuous.comp hv)
  apply hasDerivAt_sourceDirichletRoot_physicalNLS a (hu.spatial_smooth time) (hu.periodic time)
    (smoothPeriodOneSourceAt 2 (u time) (hu.spatial_smooth time) (hu.periodic time))
    (physicalNLSSourceCLM (deriv u time)) Φ H
  · rw [← physicalNLSSourceCLM_eq_smoothSource]
    exact physicalNLSSourceCLM_eq_extend (u time) (hu.periodic time)
  · exact physicalNLSSourceCLM_eq_extend (deriv u time) (hu.velocity_periodic time)
  · intro x
    rfl
  · intro x
    have he : v x = (classicalNLSVectorField a (fun y => conj (a y))).1 x :=
      (hu.equation time x).trans (congrFun (scalarClassicalNLSVectorField_eq a) x)
    exact Prod.ext he ((congrArg conj he).trans (classicalNLSVectorField_real a x).symm)
  · exact hu.hasDerivAt_hilbertSource time
  · rfl

/-- The physical velocity sign is the original sheet sign multiplied by
the explicit real NLS factor, including zero velocities and gap endpoints. -/
theorem IsClassicalNLSTrajectory.dirichletRoot_velocity_sign
    {u : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u)
    (time : ℝ) (n : ℤ) :
    let φ := fun t => smoothPeriodOneSourceAt 2 (u t) (hu.spatial_smooth t) (hu.periodic t)
    let a := fun x : ℝ => u time (x : AddCircle (2 : ℝ))
    SignType.sign (deriv (fun t => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num)
      .dirichlet (φ t).val n) time).re =
        sourceDirichletSign (by simp) (by norm_num) (φ time) n *
          SignType.sign (sourceNLSDirichletVelocityMultiplier (φ time) a n) := by
  dsimp only
  rw [(hu.hasDerivAt_dirichletRoot time n).deriv,ofReal_re,sign_mul,mul_comm]
  rfl

/-- The constructed global ordinary solution has this actual velocity at
every time and every signed Dirichlet index. -/
theorem SmoothNLSData.hasDerivAt_ordinarySource_dirichletRoot
    (f : SmoothNLSData) (time : ℝ) (n : ℤ) :
    HasDerivAt (fun t => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num)
        .dirichlet (f.ordinarySource 2 t).val n)
      ((sourceNLSDirichletVelocityMultiplier (f.ordinarySource 2 time)
          (fun x : ℝ => f.ordinary time (x : AddCircle (2 : ℝ))) n *
        (sourceAntiDiscriminantCandidate (by simp) (by norm_num) (f.ordinarySource 2 time).val
          (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
            (f.ordinarySource 2 time).val n)).re : ℝ) : ℂ) time :=
  f.ordinary_isClassical.hasDerivAt_dirichletRoot time n

/-- The direction formula for the constructed original-source solution. -/
theorem SmoothNLSData.ordinarySource_dirichletRoot_velocity_sign
    (f : SmoothNLSData) (time : ℝ) (n : ℤ) :
    SignType.sign (deriv (fun t => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num)
      .dirichlet (f.ordinarySource 2 t).val n) time).re =
        sourceDirichletSign (by simp) (by norm_num) (f.ordinarySource 2 time) n *
          SignType.sign (sourceNLSDirichletVelocityMultiplier (f.ordinarySource 2 time)
            (fun x : ℝ => f.ordinary time (x : AddCircle (2 : ℝ))) n) :=
  f.ordinary_isClassical.dirichletRoot_velocity_sign time n

end NLS.ZakharovShabat
