import NLS.KdV.HillEnergyDiscriminantGradients
import NLS.KdV.HillDirichletSheetRoot
import NLS.KdV.HillDirichletDarbouxCotangents
import NLS.KdV.HillActionDirichletBrackets

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- At its own Dirichlet energy the actual discriminant cotangent is a
precise linear combination of the log-norming and Dirichlet cotangents. -/
theorem hillEnergyDiscriminantGradient_dirichlet_decomposition
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    hillEnergyDiscriminantGradientCurve (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)=
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn) • hillLogNormingGradientCurve q n hn+
        ((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)*
          (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
              (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*hillLogNormingProjection q n hn-
            (hillDirichletCosineCurve q n hn ⟨1,by norm_num⟩).2)) • hillDirichletGradientCurve q n hn := by
  let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  let p := SpectralWeight.one.toCoeff q.val
  let S := hillDirichletStateCurve q n hn
  let C := hillDirichletCosineCurve q n hn
  let M : ℂ := scalarStateMass S
  have hM : M≠0 := ofReal_ne_zero.mpr (hillDirichletState_mass_pos q n hn).ne'
  have hzero : (S ⟨1,by norm_num⟩).1=0 := hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
  have htrace : (C ⟨1,by norm_num⟩).1+(S ⟨1,by norm_num⟩).2=hillL2Discriminant p E := by
    have ht := hillL2FrequencyStateCurve_trace p (Complex.sqrt E)
    rw [←hillL2Discriminant_sq,complex_sqrt_sq] at ht
    exact ht
  have hsheet : hillDirichletSheetRoot p E=(S ⟨1,by norm_num⟩).2-(C ⟨1,by norm_num⟩).1 := by
    unfold hillDirichletSheetRoot
    rw [←htrace]
    change 2*(S ⟨1,by norm_num⟩).2-((C ⟨1,by norm_num⟩).1+(S ⟨1,by norm_num⟩).2)=_
    ring
  ext t
  rw [hillEnergyDiscriminantGradientCurve,hillDiscriminantGradientCurve_eq_scalar_polynomial]
  change (S ⟨1,by norm_num⟩).1*(C t).1^2+
      ((S ⟨1,by norm_num⟩).2-(C ⟨1,by norm_num⟩).1)*(C t).1*(S t).1-
        (C ⟨1,by norm_num⟩).2*(S t).1^2=
      hillDirichletSheetRoot p E*((C t).1*(S t).1-hillLogNormingProjection q n hn*(S t).1^2)+
        (M*(hillDirichletSheetRoot p E*hillLogNormingProjection q n hn-(C ⟨1,by norm_num⟩).2))*
          (M⁻¹*(S t).1^2)
  rw [hzero,zero_mul,zero_add,hsheet]
  field_simp
  ring

private theorem pairing_dirichlet_spatial (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (f : Curve ℂ) :
    unitComplexCurvePairing f (hillDirichletGradientSpatialCurve q n hn)=
      ∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend f x*
        deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)) x := by
  rw [unitComplexCurvePairing_apply]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillDirichletGradientCurve q n hn] with x hx
  change NLS.LinearVolterra.extend f x*NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q n hn) x=_
  rw [hx.deriv]

/-- The coinciding-energy trace/Dirichlet bracket has its filled diagonal value,
including zero sheets and collapsed gaps. -/
theorem hillDiscriminantDirichletGardnerBracket_diagonal
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    hillDiscriminantDirichletGardnerBracket q
        (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) n hn=
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)/2 := by
  rw [←unitComplexCurvePairing_energy_dirichlet]
  rw [hillEnergyDiscriminantGradient_dirichlet_decomposition]
  simp only [map_add,add_apply,map_smul,smul_apply,smul_eq_mul]
  rw [pairing_dirichlet_spatial,pairing_dirichlet_spatial,
    hillLogDirichletGardnerBracket_eq]
  change _+_*hillDirichletGardnerBracket q n n hn hn=_
  rw [hillDirichletGardnerBracket_eq_zero,mul_zero,add_zero,if_pos rfl]
  ring

end NLS.KdV
