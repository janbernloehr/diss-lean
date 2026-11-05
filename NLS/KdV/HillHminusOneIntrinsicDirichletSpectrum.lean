import NLS.KdV.HillHminusOnePhysicalDirichlet
import NLS.KdV.HillHminusOneIntrinsicWeakConverse
import NLS.MKdV.L2QuasiHillInitialLinearity

/-! # Exact intrinsic H^-1 weak Dirichlet spectrum

The original normalized entire Dirichlet characteristic vanishes exactly
at intrinsic nonzero H1 weak Dirichlet eigenfunctions. Reconstruction in
every Miura chart shows that all such functions at a fixed energy are
nonzero scalar multiples of the actual normalized Dirichlet column.
This is geometric simplicity, not an algebraic zero-multiplicity claim.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

def IsIntrinsicHillDirichletEigenfunction (q : PeriodOneHminusOne) (lambda : ℂ) (y : Curve ℂ) : Prop :=
  y ≠ 0 ∧ AbsolutelyContinuousOnInterval (extend y) 0 1 ∧
    MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
    extend y 0 = 0 ∧ extend y 1 = 0 ∧
    ∀ φ : Curve ℂ, AbsolutelyContinuousOnInterval (extend φ) 0 1 →
      MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
      extend φ 0 = 0 → extend φ 1 = 0 →
      hillHminusWeakForm q y φ = lambda*(∫ s in (0 : ℝ)..1, extend y s*extend φ s)

theorem HillHminusMiuraChart.physicalPosition_intrinsic_dirichlet_of_zero
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (lambda : ℂ)
    (hz : hillHminusDirichlet q lambda = 0) :
    IsIntrinsicHillDirichletEigenfunction q lambda (C.physicalPosition q lambda (0,1)) := by
  have hH := C.physicalSolution_scalar_H1 q lambda (0,1)
  refine ⟨C.physicalPosition_ne_zero q lambda (0,1) (by simp),hH.1,hH.2.1,
    l2QuasiHillPosition_initial _ _ _,?_,?_⟩
  · exact (C.hillHminusDirichlet_eq_physicalPosition q hq lambda).symm.trans hz
  intro φ hφ hφ₂ hφ₀ hφ₁
  rw [hillHminusWeakForm_eq_chart C q hq _ φ hH.1 hφ hH.2.1 hφ₂
    (by rw [hφ₀,hφ₁,mul_zero,mul_zero])]
  exact C.physicalSolution_weak_equation_zero_endpoints q lambda (0,1) φ hφ hφ₂ hφ₀ hφ₁

/-- Every intrinsic weak Dirichlet function is a nonzero scalar multiple
of the same actual normalized column, in every admissible Miura chart. -/
theorem HillHminusMiuraChart.intrinsic_dirichlet_eq_scalar_column
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (lambda : ℂ)
    (y : Curve ℂ) (hy : IsIntrinsicHillDirichletEigenfunction q lambda y) :
    ∃ c : ℂ, c ≠ 0 ∧ y = c • C.physicalPosition q lambda (0,1) := by
  obtain ⟨hyn,hyAC,hy₂,hy₀,_,hw⟩ := hy
  obtain ⟨v,hv,he⟩ := exists_nonzero_initial_state_of_weak_Hill_equation
    (C.physicalProfile q) C.energyShift lambda y hyn hyAC hy₂ (by
      intro φ hφ hφ₂ hφ₀ hφ₁
      rw [← hillHminusWeakForm_eq_chart C q hq y φ hyAC hφ hy₂ hφ₂
        (by rw [hφ₀,hφ₁,mul_zero,mul_zero])]
      exact hw φ hφ hφ₂ hφ₀ hφ₁)
  have hv₁ : v.1 = 0 := by
    rw [he,l2QuasiHillPosition_initial] at hy₀
    exact hy₀
  have hv₂ : v.2 ≠ 0 := fun h => hv (Prod.ext hv₁ h)
  have hpair : v = v.2 • ((0,1) : ℂ × ℂ) := by
    apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,mul_one]
    exact hv₁
  rw [hpair,l2QuasiHillPosition_smul_initial] at he
  exact ⟨v.2,hv₂,he⟩

theorem hillHminusDirichlet_zero_of_intrinsic_dirichlet (q : PeriodOneHminusOne) (lambda : ℂ)
    (y : Curve ℂ) (hy : IsIntrinsicHillDirichletEigenfunction q lambda y) :
    hillHminusDirichlet q lambda = 0 := by
  let C := hillHminusMiuraChartAt q
  have hq : q ∈ C.domain := mem_hillHminusMiuraChartAt q
  obtain ⟨c,hc,he⟩ := C.intrinsic_dirichlet_eq_scalar_column q hq lambda y hy
  have he₁ := congrArg (fun f : Curve ℂ => extend f 1) he
  change extend y 1 = c*extend (C.physicalPosition q lambda (0,1)) 1 at he₁
  rw [hy.2.2.2.2.1,← C.hillHminusDirichlet_eq_physicalPosition q hq lambda] at he₁
  exact (mul_eq_zero.mp he₁.symm).resolve_left hc

/-- Exact equivalence at arbitrary complex energies, including zero. -/
theorem hillHminusDirichlet_eq_zero_iff_intrinsic_dirichlet (q : PeriodOneHminusOne) (lambda : ℂ) :
    hillHminusDirichlet q lambda = 0 ↔
      ∃ y : Curve ℂ, IsIntrinsicHillDirichletEigenfunction q lambda y := by
  constructor
  · intro hz
    let C := hillHminusMiuraChartAt q
    exact ⟨C.physicalPosition q lambda (0,1),C.physicalPosition_intrinsic_dirichlet_of_zero
      q (mem_hillHminusMiuraChartAt q) lambda hz⟩
  · rintro ⟨y,hy⟩
    exact hillHminusDirichlet_zero_of_intrinsic_dirichlet q lambda y hy

end NLS.KdV
