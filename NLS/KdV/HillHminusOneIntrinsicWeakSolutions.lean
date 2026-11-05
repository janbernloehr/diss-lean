import NLS.KdV.HillHminusOneWeakPotentialFunctional
import NLS.KdV.HillHminusOneWeakSpectrum

/-! # Intrinsic scalar weak Floquet solutions from the actual discriminant

The conclusion is expressed only in the original potential, scalar H1
curve, endpoint multiplier and intrinsic weak form. No Miura chart occurs
in the weak eigenfunction predicate. The converse and the intrinsic
closed/self-adjoint operator realization are not asserted here.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

/-- Nonzero H1 weak Floquet eigenfunctions of the original rough Hill
form. The test multiplier is the reciprocal state multiplier. -/
def IsIntrinsicHillWeakEigenfunction (q : PeriodOneHminusOne) (lambda σ : ℂ) (y : Curve ℂ) : Prop :=
  σ ≠ 0 ∧ y ≠ 0 ∧ AbsolutelyContinuousOnInterval (extend y) 0 1 ∧
    MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
    extend y 1 = σ*extend y 0 ∧
    ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 1 = σ⁻¹*extend φ 0 →
      hillHminusWeakForm q y φ = lambda*(∫ s in (0 : ℝ)..1, extend y s*extend φ s)

namespace HillHminusMiuraChart

theorem physicalPosition_endpoint_multiplier (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (lambda σ : ℂ) (v : ℂ × ℂ)
    (hv : C.physicalSolution q lambda v ⟨1,by constructor <;> norm_num⟩ = σ • v) :
    extend (C.physicalPosition q lambda v) 1 = σ*extend (C.physicalPosition q lambda v) 0 := by
  change (extend (C.physicalSolution q lambda v) ((⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) : ℝ)).1 = _
  rw [extend_coe]
  change (C.physicalSolution q lambda v ⟨1,by constructor <;> norm_num⟩).1 =
    σ*extend (l2QuasiHillPosition (C.physicalProfile q) (lambda+C.energyShift) v) 0
  rw [l2QuasiHillPosition_initial]
  simpa only [Prod.smul_fst,smul_eq_mul] using congrArg Prod.fst hv

/-- Every physical chart solution with reciprocal test endpoints obeys
the intrinsic rough potential equation. -/
theorem intrinsic_weak_equation_floquet (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hq : q ∈ C.domain) (lambda σ ρ : ℂ) (hσρ : σ*ρ = 1) (v : ℂ × ℂ)
    (hv : C.physicalSolution q lambda v ⟨1,by constructor <;> norm_num⟩ = σ • v)
    (φ : Curve ℂ) (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφend : extend φ 1 = ρ*extend φ 0) :
    hillHminusWeakForm q (C.physicalPosition q lambda v) φ =
      lambda*(∫ s in (0 : ℝ)..1, extend (C.physicalPosition q lambda v) s*extend φ s) := by
  have hH := C.physicalSolution_scalar_H1 q lambda v
  have hend : extend (C.physicalPosition q lambda v) 1*extend φ 1 =
      extend (C.physicalPosition q lambda v) 0*extend φ 0 := by
    rw [C.physicalPosition_endpoint_multiplier q lambda σ v hv,hφend]
    linear_combination extend (C.physicalPosition q lambda v) 0*extend φ 0*hσρ
  rw [hillHminusWeakForm_eq_chart C q hq _ φ hH.1 hφ hH.2.1 hφ₂ hend]
  exact C.physicalSolution_weak_equation_floquet q lambda σ ρ hσρ v hv φ hφ hφ₂ hφend

end HillHminusMiuraChart

/-- A characteristic multiplier of the actual entire discriminant gives
an intrinsic nonzero scalar H1 weak Floquet solution, at every energy. -/
theorem exists_intrinsic_weak_eigenfunction_of_multiplier (q : PeriodOneHminusOne) (lambda σ : ℂ)
    (hroot : σ^2-hillHminusDiscriminant q lambda*σ+1 = 0) :
    ∃ y : Curve ℂ, IsIntrinsicHillWeakEigenfunction q lambda σ y := by
  have hσ : σ ≠ 0 := by
    intro hz
    rw [hz] at hroot
    norm_num at hroot
  let C := hillHminusMiuraChartAt q
  have hq : q ∈ C.domain := mem_hillHminusMiuraChartAt q
  obtain ⟨v,hv,he⟩ := (C.hillHminusDiscriminant_multiplier_iff q hq lambda σ).mp hroot
  have hH := C.physicalSolution_scalar_H1 q lambda v
  refine ⟨C.physicalPosition q lambda v,hσ,C.physicalPosition_ne_zero q lambda v hv,hH.1,hH.2.1,
    C.physicalPosition_endpoint_multiplier q lambda σ v he,?_⟩
  intro φ hφ hφ₂ hφend
  exact C.intrinsic_weak_equation_floquet q hq lambda σ σ⁻¹ (mul_inv_cancel₀ hσ) v he φ hφ hφ₂ hφend

/-- Every canonical real root, including the lowest and closed-gap roots,
has an intrinsic nonzero scalar H1 weak eigenfunction of its indexed sign. -/
theorem exists_intrinsic_weak_eigenfunction_at_real_label (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (j : ℕ) :
    ∃ y : Curve ℂ, IsIntrinsicHillWeakEigenfunction q (hillHminusRealLabels q hr j) ((-1 : ℂ)^((j+1)/2)) y := by
  apply exists_intrinsic_weak_eigenfunction_of_multiplier
  let σ : ℂ := (-1)^((j+1)/2)
  have hσ : σ^2 = 1 := by
    dsimp only [σ]
    rw [← pow_mul,mul_comm ((j+1)/2) 2,pow_mul]
    norm_num
  rw [hillHminusRealLabels_trace_parity q hr j]
  change σ^2-2*σ*σ+1 = 0
  linear_combination -hσ

end NLS.KdV
