import NLS.Fourier.UnitIntervalDirichlet
import NLS.Fourier.UnitIntervalSobolevRealization

/-! The native zero-trace H1 domain in the EXACT unnormalized physical
L2([0,1],C) norm. Its original continuous representative is unchanged. -/
noncomputable section
open Set MeasureTheory
namespace NLS.Fourier
open NLS.ZakharovShabat
local instance dirichletL2H1NormedGroup : NormedAddCommGroup UnitDirichletH1 :=
  unitDirichletSubspace.normedAddCommGroup
local instance dirichletL2H1NormedSpace : NormedSpace ℂ UnitDirichletH1 :=
  unitDirichletSubspace.normedSpace

/-- Actual physical interval L2 inclusion of the full native Dirichlet domain. -/
def unitDirichletL2Inclusion : UnitDirichletH1 →L[ℂ] IntervalL2 :=
  unitL2SynthesisEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (scalarInclusion.comp unitDirichletSubspace.subtypeL)

/-- The L2 class is the IDENTICAL original native interval representative a.e. -/
theorem unitDirichletL2Inclusion_representative (f : UnitDirichletH1) :
    unitDirichletL2Inclusion f =ᵐ[volume.restrict (Ioc 0 1)] unitDirichletRepresentative f :=
  unitL2Synthesis_scalarInclusion f.val

/-- The coefficient and physical interval L2 norms agree EXACTLY. -/
theorem norm_unitDirichletL2Inclusion (f : UnitDirichletH1) :
    ‖unitDirichletL2Inclusion f‖ = ‖scalarInclusion f.val‖ :=
  unitL2SynthesisEquiv.norm_map _

/-- No native Dirichlet domain vector is lost by its physical L2 inclusion. -/
theorem unitDirichletL2Inclusion_injective : Function.Injective unitDirichletL2Inclusion := by
  intro f g he
  apply Subtype.ext
  apply scalarInclusion_injective
  exact unitL2SynthesisEquiv.injective he

/-- The actual norm is the literal unnormalized unit-interval integral. -/
theorem norm_sq_unitDirichletL2Inclusion (f : UnitDirichletH1) :
    ‖unitDirichletL2Inclusion f‖^2 =
      ∫ x in (0:ℝ)..1, ‖unitDirichletRepresentative f x‖^2 := by
  rw [norm_sq_intervalL2]
  simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [unitDirichletL2Inclusion_representative f] with x hx
  rw [hx]

end NLS.Fourier
