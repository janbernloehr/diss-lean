import NLS.KdV.HminusOneDirichletProjectionConvergence

/-! Exact identification of the ACTUAL free source contour projection
with its physical sine kernel and the unnormalized-interval factor TWO. -/
noncomputable section
open Set Metric Complex MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat
local instance dirichletFreeRieszH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletFreeRieszH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace

/-- The actual zero-potential source contour operator is the literal free
sine projector on every sufficiently high original circle. The factor two
is PROVED from the exact physical sine square integral one half. -/
theorem exists_dirichletFreeRieszProjection_sine_kernel :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ+, N < (n:ℕ) → ∀ F : IntervalL2,
      ∀ x : Icc (0:ℝ) 1,
        singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) F x =
          (2*(∫ y in (0:ℝ)..1, F y*sin ((Real.pi:ℂ)*(n:ℕ)*y)))*
            sin ((Real.pi:ℂ)*(n:ℕ)*x.val) := by
  obtain ⟨N,V,hN,_,hzero,_,hcircles⟩ := exists_uniform_hillHminusDirichlet_sourceCircles 0
  refine ⟨N,hN,?_⟩
  intro n hn F x
  obtain ⟨hc,hl,hiso,hm⟩ := hcircles 0 hzero n hn
  simp only [map_zero,hillHminusDirichletComplexLabels_zero] at hc hl hiso hm
  have hr : (0:ℝ) < (n:ℝ) := by exact_mod_cast n.property
  have honly (z : ℂ) (hz : z ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ))
      (hs : z ∈ singularDirichletSpectrum 0) : z = ((Real.pi:ℂ)*(n:ℕ))^2 :=
    (hiso z (ball_subset_closedBall hz)).mp hs
  obtain ⟨h,hh0,hh,hhC⟩ := exists_native_freeDirichlet_sine n
  have hpos (y : ℝ) (hy : y ∈ Icc (0:ℝ) 1) :
      unitDirichletRepresentative h y = sin ((Real.pi:ℂ)*(n:ℕ)*y) := by
    exact congrArg (fun K : C(Icc (0:ℝ) 1,ℂ) => K ⟨y,hy⟩) hhC
  have hnum : singularDirichletL2BaseInclusion F h =
      ∫ y in (0:ℝ)..1, F y*sin ((Real.pi:ℂ)*(n:ℕ)*y) := by
    rw [singularDirichletL2BaseInclusion_representative_pairing]
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hy
    dsimp only
    rw [hpos y hy']
  change unitDirichletContinuousInclusion (singularDirichletRieszToH1 0 _ _
    (singularDirichletL2BaseInclusion F)) x = _
  rw [singularDirichletRieszToH1_eq_pairing_smul 0 _ _ hr hc _ hl honly hm h hh0 hh,
    map_smul,ContinuousMap.smul_apply]
  change (singularDirichletL2BaseInclusion F h/singularDirichletDomainInclusion h h)*
    unitDirichletRepresentative h x.val = _
  rw [hnum,singularDirichlet_mass_of_freeSine n h hhC,hpos x.val x.property]
  ring

end NLS.KdV
