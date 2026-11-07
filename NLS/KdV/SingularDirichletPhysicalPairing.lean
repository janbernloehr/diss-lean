import NLS.KdV.SingularDirichletL2Base
import NLS.ZakharovShabat.PhysicalL2BilinearPairing

/-! The faithful physical L2 inclusion into the FULL native Dirichlet dual
is exactly the unnormalized physical bilinear integral, on every native test. -/
noncomputable section
open Set MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat
local instance dirichletPhysicalPairingH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletPhysicalPairingH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletPhysicalPairingBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletPhysicalPairingBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- The actual L2-to-native-dual inclusion evaluates by the ORIGINAL unit
interval integral, with no conjugation or extra normalization factor. -/
theorem singularDirichletL2BaseInclusion_pairing (F : IntervalL2) (g : UnitDirichletH1) :
    singularDirichletL2BaseInclusion F g =
      ∫ x in (0:ℝ)..1, F x*unitDirichletL2Inclusion g x := by
  let a := unitL2SynthesisEquiv.symm F
  have he : singularDirichletL2BaseInclusion F g =
      ∑' n : ℤ, a (-n)*g.val.val n := by
    change WeightedCoeff.sobolevDualityIsometry (p := 2) (q := 2) 1 (by norm_num)
      (periodOneL2Inclusion a) g.val = _
    rw [WeightedCoeff.sobolevDualityIsometry_apply,WeightedCoeff.sobolevBilinearPairing_apply]
    exact tsum_congr fun n => by rw [periodOneL2Inclusion_apply]; ring
  have hp := physicalL2_reflected_pairing (Coeff.reflection a) (scalarInclusion g.val)
  rw [Coeff.reflection_reflection] at hp
  change (∫ x in (0:ℝ)..1, unitL2SynthesisEquiv a x*unitDirichletL2Inclusion g x) = _ at hp
  have ha : unitL2SynthesisEquiv a = F := unitL2SynthesisEquiv.apply_symm_apply F
  rw [ha,Coeff.dualPairing_apply] at hp
  rw [hp,he]
  exact tsum_congr fun n => by rw [Coeff.reflection_apply,scalarInclusion_apply]

/-- Physical Cauchy--Schwarz controls the ACTUAL full-dual evaluation by
the ordinary interval L2 norms, with constant exactly one. -/
theorem norm_singularDirichletL2BaseInclusion_pairing_le
    (F : IntervalL2) (g : UnitDirichletH1) :
    ‖singularDirichletL2BaseInclusion F g‖ ≤ ‖F‖*‖unitDirichletL2Inclusion g‖ := by
  let a := unitL2SynthesisEquiv.symm F
  have hp := physicalL2_reflected_pairing (Coeff.reflection a) (scalarInclusion g.val)
  rw [Coeff.reflection_reflection] at hp
  have ha : unitL2SynthesisEquiv a = F := unitL2SynthesisEquiv.apply_symm_apply F
  change (∫ x in (0:ℝ)..1, unitL2SynthesisEquiv a x*unitDirichletL2Inclusion g x) = _ at hp
  rw [ha,← singularDirichletL2BaseInclusion_pairing] at hp
  rw [hp,norm_unitDirichletL2Inclusion]
  have hb := Coeff.norm_dualPairing_le (Coeff.reflection a) (scalarInclusion g.val)
  simpa only [a,LinearIsometryEquiv.norm_map] using hb

/-- The native mass of two Dirichlet vectors is EXACTLY their physical
bilinear L2 integral, retaining the full original domain. -/
theorem singularDirichletDomainInclusion_physical_pairing (f g : UnitDirichletH1) :
    singularDirichletDomainInclusion f g =
      ∫ x in (0:ℝ)..1, unitDirichletL2Inclusion f x*unitDirichletL2Inclusion g x := by
  rw [← singularDirichletL2BaseInclusion_domain f,singularDirichletL2BaseInclusion_pairing]

/-- The same evaluation uses the IDENTICAL original continuous representative. -/
theorem singularDirichletL2BaseInclusion_representative_pairing
    (F : IntervalL2) (g : UnitDirichletH1) :
    singularDirichletL2BaseInclusion F g =
      ∫ x in (0:ℝ)..1, F x*unitDirichletRepresentative g x := by
  rw [singularDirichletL2BaseInclusion_pairing]
  simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [unitDirichletL2Inclusion_representative g] with x hx
  rw [hx]

/-- The native bilinear mass is the literal integral of the continuous
original position product, including both endpoint conditions. -/
theorem singularDirichletDomainInclusion_representative_pairing (f g : UnitDirichletH1) :
    singularDirichletDomainInclusion f g =
      ∫ x in (0:ℝ)..1, unitDirichletRepresentative f x*unitDirichletRepresentative g x := by
  rw [singularDirichletDomainInclusion_physical_pairing]
  simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [unitDirichletL2Inclusion_representative f,
    unitDirichletL2Inclusion_representative g] with x hx hy
  rw [hx,hy]

end NLS.KdV
