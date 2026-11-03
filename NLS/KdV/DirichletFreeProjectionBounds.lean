import NLS.KdV.DirichletFreeRieszKernel

/-! Uniform bounds and the literal sine fixed vector of the ACTUAL free
Dirichlet contour projection, in the original unnormalized interval norms. -/
noncomputable section
open Set Metric Complex MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat
local instance freeProjectionH1Group : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance freeProjectionH1Space : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace

/-- The actual free projection is uniformly bounded by two in both
physical operator norms, and fixes the literal sine with its exact mass. -/
theorem exists_dirichletFreeProjection_bounds_and_sine_fixed :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ+, N < (n:ℕ) →
      ‖singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤ 2 ∧
      ‖singularDirichletL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤ 2 ∧
      singularDirichletL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)
        (unitIntervalContinuousToLp 2 (dirichletFreeSineCurve n)) =
          unitIntervalContinuousToLp 2 (dirichletFreeSineCurve n) := by
  obtain ⟨N,hN,hkernel⟩ := exists_dirichletFreeRieszProjection_sine_kernel
  refine ⟨N,hN,?_⟩
  intro n hn
  obtain ⟨h,_,_,hh⟩ := exists_native_freeDirichlet_sine n
  have hpos (y : ℝ) (hy : y ∈ Icc (0:ℝ) 1) :
      unitDirichletRepresentative h y = sin ((Real.pi:ℂ)*(n:ℕ)*y) :=
    congrArg (fun K : C(Icc (0:ℝ) 1,ℂ) => K ⟨y,hy⟩) hh
  have hnum (F : IntervalL2) : singularDirichletL2BaseInclusion F h =
      ∫ y in (0:ℝ)..1, F y*sin ((Real.pi:ℂ)*(n:ℕ)*y) := by
    rw [singularDirichletL2BaseInclusion_representative_pairing]
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Icc (0:ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hy
    dsimp only
    rw [hpos y hy']
  have hformula (F : IntervalL2) :
      singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) F =
        (2*singularDirichletL2BaseInclusion F h) • dirichletFreeSineCurve n := by
    apply ContinuousMap.ext
    intro x
    rw [hkernel n hn F x,ContinuousMap.smul_apply,hnum]
    rfl
  have hL : ‖unitDirichletL2Inclusion h‖ ≤ 1 := by
    apply (norm_unitDirichletL2Inclusion_le_uniform h).trans
    rw [hh]
    exact norm_dirichletFreeSineCurve_le_one n
  have hC : ‖singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro F
    rw [hformula,norm_smul,norm_mul]
    norm_num only [Complex.norm_ofNat]
    have hp := norm_singularDirichletL2BaseInclusion_pairing_le F h
    have hs := norm_dirichletFreeSineCurve_le_one n
    calc
      _ ≤ 2*(‖F‖*‖unitDirichletL2Inclusion h‖)*1 := by gcongr
      _ ≤ 2*‖F‖ := by nlinarith [norm_nonneg F]
  refine ⟨hC,?_,?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro F
    rw [singularDirichletL2RieszProjection_eq_continuousToLp]
    exact (norm_unitIntervalContinuousToLp_le 2 _).trans
      (((singularDirichletContinuousRieszProjection 0 _ _).le_opNorm F).trans
        (mul_le_mul_of_nonneg_right hC (norm_nonneg F)))
  · rw [← hh,unitIntervalContinuousToLp_two_dirichlet,
      singularDirichletL2RieszProjection_eq_continuousToLp,hformula,
      singularDirichletL2BaseInclusion_domain,singularDirichlet_mass_of_freeSine n h hh]
    norm_num
    rw [← hh]
    exact unitIntervalContinuousToLp_two_dirichlet h

end NLS.KdV
