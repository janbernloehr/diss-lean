import NLS.KdV.HillHminusOnePhysicalDirichlet
import NLS.KdV.HillHminusOneRealMiuraCharts
import NLS.MKdV.L2QuasiHillDirichletGauge
import NLS.ZakharovShabat.L2SourceCharacteristics

/-! # Exact source Dirichlet coordinates for every rough Hill Miura chart

The coefficient map u -> (i*u,-i*u) has exactly the physical rotated
profile used by the rough integral intertwiner. Its original normalized
source characteristic is z*S(q,z^2-c), not an unspecified nonzero factor.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ComplexConjugate
open NLS.Fourier NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

def hillDirichletMiuraSource : Coeff 2 →L[ℂ] CoeffPair 2 :=
  I • (CoeffPair.inlCLM (p := 2))+(-I) • (CoeffPair.inrCLM (p := 2))

@[simp] theorem hillDirichletMiuraSource_fst (u : Coeff 2) :
    (hillDirichletMiuraSource u).fst = I • u := by
  change I • u+(-I) • 0 = _
  simp

@[simp] theorem hillDirichletMiuraSource_snd (u : Coeff 2) :
    (hillDirichletMiuraSource u).snd = (-I) • u := by
  change I • 0+(-I) • u = _
  simp

theorem sourcePhysicalL2_hillDirichletMiuraSource (u : Coeff 2) :
    sourcePhysicalL2 (hillDirichletMiuraSource u) = intervalL2DirichletMiura (unitL2SynthesisEquiv u) := by
  rw [← sourcePhysicalL2Equiv_apply]
  apply WithLp.ofLp_injective
  change (unitL2SynthesisEquiv (hillDirichletMiuraSource u).fst,
    unitL2SynthesisEquiv (hillDirichletMiuraSource u).snd) = (I • unitL2SynthesisEquiv u,(-I) • unitL2SynthesisEquiv u)
  rw [hillDirichletMiuraSource_fst,hillDirichletMiuraSource_snd,map_smul,map_smul]

theorem hillDirichletMiuraSource_real (u : Coeff 2)
    (hu : ∀ k : ℤ, u (-k) = conj (u k)) :
    IsRealType (CoeffPair.toMax 2 (hillDirichletMiuraSource u)) := by
  intro k
  change ((hillDirichletMiuraSource u).snd) k = conj (((hillDirichletMiuraSource u).fst) (-k))
  rw [hillDirichletMiuraSource_fst,hillDirichletMiuraSource_snd]
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,map_mul,hu,conj_conj,conj_I]

theorem periodOneBoundaryCharacteristic_dirichletMiura (u : Coeff 2) (z : ℂ) :
    periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (hillDirichletMiuraSource u) z =
        z*extend (l2QuasiHillPosition (unitL2SynthesisEquiv u) (z^2) (0,1)) 1 := by
  rw [periodOneBoundaryCharacteristic_eq_l2,sourcePhysicalL2_hillDirichletMiuraSource,
    l2SeparatedCharacteristic_dirichletMiura]

theorem periodOneBoundaryCharacteristic_dirichletMiura_zero (u : Coeff 2) :
    periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet (hillDirichletMiuraSource u) 0 = 0 := by
  rw [periodOneBoundaryCharacteristic_dirichletMiura,zero_mul]

theorem HillHminusMiuraChart.dirichlet_source_real (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hreal : star (C.physicalProfile q) = C.physicalProfile q) :
    IsRealType (CoeffPair.toMax 2 (hillDirichletMiuraSource (C.lift q))) := by
  apply hillDirichletMiuraSource_real
  intro k
  have he := congrArg (fun v : IntervalL2 => intervalFourierCoefficient 1 v (-k)) hreal
  rw [intervalFourierCoefficient_Lp_star,C.physicalProfile_coefficient,
    C.physicalProfile_coefficient,neg_neg] at he
  exact he.symm

theorem HillHminusMiuraChart.dirichlet_source_characteristic (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (z : ℂ) :
    periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (hillDirichletMiuraSource (C.lift q)) z = z*hillHminusDirichlet q (z^2-C.energyShift) := by
  rw [periodOneBoundaryCharacteristic_eq_l2,sourcePhysicalL2_hillDirichletMiuraSource,
    l2SeparatedCharacteristic_dirichletMiura,C.hillHminusDirichlet_eq_physicalPosition q hq]
  change z*extend (l2QuasiHillPosition (C.physicalProfile q) (z^2) (0,1)) 1 =
    z*extend (l2QuasiHillPosition (C.physicalProfile q) (z^2-C.energyShift+C.energyShift) (0,1)) 1
  rw [sub_add_cancel]

theorem HillHminusMiuraChart.dirichlet_source_zero_iff (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (z : ℂ) (hz : z ≠ 0) :
    periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (hillDirichletMiuraSource (C.lift q)) z = 0 ↔
        hillHminusDirichlet q (z^2-C.energyShift) = 0 := by
  rw [C.dirichlet_source_characteristic q hq,mul_eq_zero,or_iff_right hz]

end NLS.KdV
