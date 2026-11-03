import NLS.KdV.SingularDirichletMiuraRegularity
import NLS.KdV.SingularDirichletOperatorDomain
import NLS.KdV.SingularHillConstantShift
import NLS.KdV.HminusOneDirichletEigenstate
import NLS.MKdV.QuasiHillL2IntervalState

/-! # Native Dirichlet eigenvectors force the original characteristic to vanish

The weak H1-to-H-minus-one eigen-equation is converted to an actual absolutely
continuous quasi-derivative state. This proves the necessary characteristic
condition for EVERY complex original H-minus-one source potential. The reverse
implication, full operator spectrum and algebraic multiplicities remain separate.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat NLS.MKdV

/-- Every native Miura eigenvector is the scalar position of an actual physical
Dirichlet state, at every point of the original closed interval. -/
theorem exists_quasiHill_state_of_native_Miura_eigen (u : Coeff 2) (lambda : ℂ)
    (f : UnitDirichletH1)
    (he : singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f =
      lambda • singularDirichletDomainInclusion f) :
    ∃ w : Curve (ℂ × ℂ), IsQuasiHillL2DirichletState u lambda w ∧
      ∀ t : Icc (0:ℝ) 1, (w t).1 = unitDirichletRepresentative f t.val := by
  obtain ⟨G, hGc, hGa, _, hQG, hGd, _⟩ :=
    exists_intervalH1_quasiDerivative_of_native_eigen u lambda f he
  have hYc : Continuous (unitDirichletRepresentative f) :=
    continuous_periodOneSobolevSynthesis f.val
  let w := quasiHillIntervalState (unitDirichletRepresentative f) G hYc hGc
  refine ⟨w, ⟨?_, ?_, ?_⟩, fun _ => rfl⟩
  · exact isQuasiHillL2Solution_intervalState u lambda _ G hYc hGc
      (absolutelyContinuous_unitDirichletRepresentative f) hGa
      (native_Miura_first_row u f G hQG) hGd
  · exact unitDirichletRepresentative_zero f
  · exact unitDirichletRepresentative_one f

/-- A nonzero native Miura eigenvector has a genuine normalized characteristic zero. -/
theorem quasiHillL2Dirichlet_eq_zero_of_native_eigen (u : Coeff 2) (lambda : ℂ)
    (f : UnitDirichletH1) (hf : f ≠ 0)
    (he : singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f =
      lambda • singularDirichletDomainInclusion f) :
    quasiHillL2Dirichlet u lambda = 0 := by
  obtain ⟨w, hw, hpos⟩ := exists_quasiHill_state_of_native_Miura_eigen u lambda f he
  apply (quasiHillL2Dirichlet_eq_zero_iff_exists_eigenstate u lambda).mpr
  refine ⟨w, hw, ?_⟩
  by_contra! hz
  apply hf
  apply unitDirichletRepresentative_injective_on_interval f 0
  intro x hx
  have hy : unitDirichletRepresentative f x = 0 := (hpos ⟨x,hx⟩).symm.trans (hz ⟨x,hx⟩)
  rw [hy]
  change (0:ℂ) = periodOneSobolevSynthesis (0 : ScalarDomain 2) (x : AddCircle (2:ℝ))
  rw [map_zero]
  rfl

/-- Constant translation of a source potential adds exactly the same scalar
multiple of the native Dirichlet domain inclusion. -/
theorem singularDirichletOperator_source_add_constant (q : PeriodOneHminusOne) (c : ℂ) :
    singularDirichletOperator (periodOneOriginal (q+periodOneL2Inclusion (lp.single 2 0 c))) =
      singularDirichletOperator (periodOneOriginal q)+c • singularDirichletDomainInclusion := by
  apply ContinuousLinearMap.ext
  intro f
  change singularDirichletRestriction
    (singularHillOperator (periodOneOriginal (q+periodOneL2Inclusion (lp.single 2 0 c)))
      (unitDirichletOriginalH1 f)) = _
  rw [periodOneOriginal_add_constant, singularHillOperator_add_constant]
  change singularDirichletRestriction
    (singularHillOperator (periodOneOriginal q) (unitDirichletOriginalH1 f)+
      c • singularHillDomainInclusion (unitDirichletOriginalH1 f)) = _
  rw [map_add, map_smul]
  rfl

/-- EVERY original complex H-minus-one native Dirichlet eigenvector is detected
by the independently constructed normalized characteristic. No realness,
nonzero energy, high-frequency cutoff or supplied Miura lift is assumed. -/
theorem hillHminusDirichlet_eq_zero_of_native_eigen (q : PeriodOneHminusOne) (lambda : ℂ)
    (f : UnitDirichletH1) (hf : f ≠ 0)
    (he : singularDirichletOperator (periodOneOriginal q) f =
      lambda • singularDirichletDomainInclusion f) :
    hillHminusDirichlet q lambda = 0 := by
  let C := hillHminusMiuraChartAt q
  have hi := C.image q (mem_hillHminusMiuraChartAt q)
  rw [hillHminusDirichlet_eq_miura_of_shifted_image q (C.lift q) C.energyShift lambda hi]
  apply quasiHillL2Dirichlet_eq_zero_of_native_eigen (C.lift q) (lambda+C.energyShift) f hf
  rw [hi, singularDirichletOperator_source_add_constant]
  change singularDirichletOperator (periodOneOriginal q) f+
    C.energyShift • singularDirichletDomainInclusion f = _
  rw [he]
  exact (add_smul lambda C.energyShift (singularDirichletDomainInclusion f)).symm

/-- The same necessity is stated for the actual partial operator on H-minus-one,
with its full zero-trace H1 domain and nonzero base-space eigenvector. -/
theorem hillHminusDirichlet_eq_zero_of_partial_eigen (q : PeriodOneHminusOne) (lambda : ℂ)
    (hv : ∃ v : (singularDirichletPartialOperator (periodOneOriginal q)).domain,
      v.val ≠ 0 ∧ singularDirichletPartialOperator (periodOneOriginal q) v = lambda • v.val) :
    hillHminusDirichlet q lambda = 0 := by
  obtain ⟨f, hf, he⟩ := (singularDirichletPartialOperator_eigen_iff
    (periodOneOriginal q) lambda).mp hv
  exact hillHminusDirichlet_eq_zero_of_native_eigen q lambda f hf
    ((singularDirichletPencil_eq_zero_iff (periodOneOriginal q) lambda f).mp he)

end NLS.KdV
