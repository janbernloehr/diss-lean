import NLS.KdV.HillPhysicalFrequencyMoments

/-! # Finite physical quartic cotangents for the frequency construction

At every real original source the finite sum has an actual analytic
source germ. Its value is the checked free-circle energy period, and its
coordinate phase consists of the exact free frequency and a finite sum
of physical second moments. Passing these cotangents to the full energy
and matching the rough Miura sums remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.KdV NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.Articles.KdVConvexity
variable (q : RealPeriodOneHillPotential)

def physicalPartialQuarticGerm (N : ℕ) (p : Coeff 2) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, hillRealSourceQuarticContour q
    (hillRealGapCenter q.val q.property.1 q.property.2 k:ℂ)
    (hillRealGapHalfLength q.val q.property.1 q.property.2 k+
      hillRealGapCollar q.val q.property.1 q.property.2 k) p

theorem analyticAt_physicalPartialQuarticGerm (N : ℕ) :
    AnalyticAt ℂ (physicalPartialQuarticGerm q N) (SpectralWeight.one.toCoeff q.val) := by
  apply Finset.analyticAt_fun_sum
  intro k hk
  have hk1 := (Finset.mem_Icc.mp hk).1
  exact analyticAt_hillRealSourceQuarticContour q _ _
    (add_nonneg (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk1).1
      (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk1).2.1.le)
    (hillRealGapContour_sphere_subset q.val q.property.1 q.property.2 k hk1)

theorem physicalPartialQuarticGerm_eq_freeQuarticPeriod
    (N : ℕ) (hN : 2≤N) (hcut : 8*‖q.val‖≤(N:ℝ))
    (hground : -(hillFreeBandFrequency N)^2<hillLowestEnergy q.val q.property.1 q.property.2) :
    physicalPartialQuarticGerm q N (SpectralWeight.one.toCoeff q.val) =
      hillL2FreeQuarticPeriod (SpectralWeight.one.toCoeff q.val) N := by
  rw [hillL2FreeQuarticPeriod_eq_partial_moments q.val q.property.1 q.property.2 N hN hcut hground]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 := (Finset.mem_Icc.mp hk).1
  rw [hillRealSourceQuarticContour_eq_physical q _ _
    (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk1).1
      (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk1).2.1) q]
  exact hillL2QuarticGapPeriod_eq_action_and_cubic q.val q.property.1 q.property.2 k hk1

def physicalPartialQuarticDirection (N : ℕ) : Coeff 2 :=
  ∑ k ∈ Finset.Icc 1 N, hillQuarticContourDirection q
    (hillRealGapCenter q.val q.property.1 q.property.2 k:ℂ)
    (hillRealGapHalfLength q.val q.property.1 q.property.2 k+
      hillRealGapCollar q.val q.property.1 q.property.2 k)

/-- A finite exact phase formula for the original physical coordinates.
This is a theorem about actual coefficient directions, not a definition
of the physical KdV frequency. -/
theorem physicalPartialQuarticDirection_coordinate_phase
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (N n : ℕ) (hn : 1≤n) (C : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q.val)) (physicalPartialQuarticDirection q N) =
      I*((8*(Real.pi:ℂ)^3*(n:ℂ)^3)*(if n∈Finset.Icc 1 N then 1 else 0) -
        12*∑ k ∈ Finset.Icc 1 N, (k:ℂ)*hillPhysicalFrequencyMoment q.val q.property.1 q.property.2 n hn k 2)*
          hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn := by
  unfold physicalPartialQuarticDirection
  rw [map_sum]
  have he := fun (k : ℕ) (hk : k∈Finset.Icc 1 N) => fderiv_hillDirichletAbelianCoordinate_extension_quarticGapDirection
    q.val q.property.1 q.property.2 h0q h0r n hn k (Finset.mem_Icc.mp hk).1 C hC hmatch
  rw [Finset.sum_congr rfl he]
  rw [← Finset.sum_mul,← Finset.mul_sum,Finset.sum_sub_distrib]
  have hfree : (∑ k ∈ Finset.Icc 1 N, (8*(Real.pi:ℂ)^3*(k:ℂ)^3)*(if k=n then 1 else 0)) =
      (8*(Real.pi:ℂ)^3*(n:ℂ)^3)*(if n∈Finset.Icc 1 N then 1 else 0) := by
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq']
  rw [hfree,Finset.mul_sum]
  simp only [mul_assoc]

end NLS.Articles.KdVConvexity
