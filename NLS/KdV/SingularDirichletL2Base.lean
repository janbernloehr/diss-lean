import NLS.KdV.SingularDirichletDenseDomain
import NLS.Fourier.UnitDirichletL2
import NLS.SequenceSpaces.CoefficientDecay

/-! Ordinary physical L2([0,1],C) data in the FULL native Dirichlet dual.
The inclusion agrees EXACTLY with the original domain inclusion. -/
noncomputable section
open Set MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat
local instance dirichletL2BaseH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletL2BaseH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletL2BaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletL2BaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- ALL ordinary interval L2 data, included in the original full continuous dual. -/
def singularDirichletL2BaseInclusion : IntervalL2 →L[ℂ] UnitDirichletHminus :=
  unitDirichletDualRestriction.comp
    ((WeightedCoeff.sobolevDualityIsometry (p := 2) (q := 2) 1 (by norm_num)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (periodOneL2Inclusion.comp unitL2SynthesisEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap))

/-- Exact mass-form identity on EVERY original native domain vector. -/
theorem singularDirichletL2BaseInclusion_domain (f : UnitDirichletH1) :
    singularDirichletL2BaseInclusion (unitDirichletL2Inclusion f) = singularDirichletDomainInclusion f := by
  have hm : periodOneL2Inclusion (scalarInclusion f.val) = unitHillMass f.val := by
    apply Subtype.ext
    funext n
    rw [periodOneL2Inclusion_apply,unitHillMass_coefficient,scalarInclusion_apply]
  rw [singularDirichletDomainInclusion_eq_restricted_mass]
  change unitDirichletDualRestriction
    (WeightedCoeff.sobolevDualityIsometry (p := 2) (q := 2) 1 (by norm_num)
      (periodOneL2Inclusion (unitL2SynthesisEquiv.symm (unitL2SynthesisEquiv (scalarInclusion f.val))))) =
    unitDirichletDualRestriction (unitHillMassDual f.val)
  rw [LinearIsometryEquiv.symm_apply_apply,hm]
  rfl

/-- No ordinary L2 data are lost when restricting to all native Dirichlet tests. -/
theorem singularDirichletL2BaseInclusion_injective : Function.Injective singularDirichletL2BaseInclusion := by
  apply (injective_iff_map_eq_zero singularDirichletL2BaseInclusion).mpr
  intro F hF
  let a := unitL2SynthesisEquiv.symm F
  let B : ScalarDomain 2 →L[ℂ] ℂ :=
    WeightedCoeff.sobolevDualityIsometry (p := 2) (q := 2) 1 (by norm_num) (periodOneL2Inclusion a)
  have hB : unitDirichletDualRestriction B = 0 := hF
  have he := (unitDirichletDualRestriction_eq_zero_iff B).mp hB
  have hmode (n : ℤ) : B (scalarMode n 1) = a (-n) := by
    dsimp only [B]
    rw [WeightedCoeff.sobolevDualityIsometry_apply,WeightedCoeff.sobolevBilinearPairing_apply]
    simp only [scalarMode_apply,ite_mul,one_mul,zero_mul,tsum_ite_eq,periodOneL2Inclusion_apply]
  have hc (n : ℤ) : a (-n) = B (scalarMode 0 1) := by
    have hn := congrArg (fun G : ScalarDomain 2 →L[ℂ] ℂ => G (scalarMode n 1)) he
    rw [hmode n] at hn
    simpa only [_root_.smul_apply,unitDirichletTrace_scalarMode,smul_eq_mul,mul_one] using hn
  have hzero : B (scalarMode 0 1) = 0 := by
    by_contra hn
    have hp : 0 < ‖B (scalarMode 0 1)‖/2 := by positivity
    obtain ⟨N,hN⟩ := Coeff.exists_cutoff_norm_apply_lt (by norm_num) a hp
    have hh := hN (N:ℤ) (by simp)
    rw [show a (N:ℤ) = B (scalarMode 0 1) from by simpa only [neg_neg] using hc (-(N:ℤ))] at hh
    linarith [norm_pos_iff.mpr hn]
  have ha : a = 0 := by
    ext n
    have hh := hc (-n)
    simpa only [neg_neg,hzero,lp.coeFn_zero,Pi.zero_apply] using hh
  apply unitL2SynthesisEquiv.symm.injective
  exact ha.trans (map_zero _).symm

end NLS.KdV
