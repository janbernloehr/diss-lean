import NLS.KdV.HillFilledPrimitiveRootQuotient
import NLS.KdV.HillQuarticContourVariation
import NLS.KdV.FrequencyMoments

/-! # Actual physical Hill moments in the quartic coordinate phase law

The filled primitive/root quotient kills odd moments on every intrinsic
gap, including a collapsed gap. The cubic phase coefficient is exactly
8*pi^3*k^3 times the normalized zeroth period minus 12*k times the raw
second moment. Identification with the full KdV frequency still requires
the full physical energy cotangent and a convergent sum over all gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillPhysicalFrequencyMoment (n : ℕ) (hn : 1≤n) (k m : ℕ) : ℂ :=
  frequencyMoment
    (fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E+I*(k:ℂ)*Real.pi)
    (fun E => hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E)
    (hillRealGapCenter q hq hr k:ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) m

theorem hillPhysicalFrequencyMoment_odd_eq_zero
    (n : ℕ) (hn : 1≤n) (k : ℕ) (hk : 1≤k) (l : ℕ) :
    hillPhysicalFrequencyMoment q hq hr n hn k (2*l+1)=0 := by
  have hrad := hillRealGapContour_geometry q hq hr k hk
  have hR := add_nonneg hrad.1 hrad.2.1.le
  have hsub := closedBall_subset_ball (x := (hillRealGapCenter q hq hr k:ℂ)) (show
    hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k <
      hillRealGapHalfLength q hq hr k+2*hillRealGapCollar q hq hr k by linarith [hrad.2.1])
  apply frequencyMoment_odd_eq_zero_of_continuations _ _
    (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) k)
    (fun E => hillFilledPrimitiveRootQuotient (SpectralWeight.one.toCoeff q) k E *
      hillAbelianSelectedGlobalPsi q hq hr n hn E) _ _ hR
  · exact (analyticOnNhd_hillL2RealGapPrimitiveSquare q hq hr k hk).mono hsub
  · exact ((analyticOnNhd_hillFilledPrimitiveRootQuotient q hq hr k hk).mul
      ((analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn).mono (subset_univ _))).mono hsub
  · intro E hE
    refine ⟨rfl,?_⟩
    rw [hillFilledPrimitiveRootQuotient_eq_physical q hq hr k E
      (hillRealGapContour_sphere_subset q hq hr k hk hE)]
    ring

theorem hillPhysicalFrequencyMoment_zero
    (n : ℕ) (hn : 1≤n) (k : ℕ) (hk : 1≤k) :
    hillPhysicalFrequencyMoment q hq hr n hn k 0 = (2*(Real.pi:ℂ))*(if k=n then 1 else 0) := by
  have hp := hillAbelianSelectedGlobalPsi_intrinsic_periods q hq hr n hn k hk
  have he : hillPhysicalFrequencyMoment q hq hr n hn k 0 =
      ∮ E in C((hillRealGapCenter q hq hr k:ℂ),
        hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E := by
    unfold hillPhysicalFrequencyMoment frequencyMoment
    simp only [pow_zero,one_mul]
    apply circleIntegral.integral_congr
      (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
        (hillRealGapContour_geometry q hq hr k hk).2.1.le)
    intro E hE
    dsimp only []
    rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr
      (hillRealGapContour_sphere_subset q hq hr k hk hE)]
  rw [he]
  have hpi : (2*(Real.pi:ℂ))≠0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  calc
    _ = (2*(Real.pi:ℂ))*((2*(Real.pi:ℂ))⁻¹ * _) := by rw [← mul_assoc,mul_inv_cancel₀ hpi,one_mul]
    _ = _ := by rw [hp]

/-- The actual cubic energy period reduces to the physical second
moment and the globally normalized Kronecker period. -/
theorem hillPhysicalCubicPeriod_eq_secondMoment
    (n : ℕ) (hn : 1≤n) (k : ℕ) (hk : 1≤k) :
    (∮ E in C((hillRealGapCenter q hq hr k:ℂ),
      hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3 *
        hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E) =
      -3*(I*(k:ℂ)*Real.pi)*hillPhysicalFrequencyMoment q hq hr n hn k 2 -
        (I*(k:ℂ)*Real.pi)^3*hillPhysicalFrequencyMoment q hq hr n hn k 0 := by
  let F := fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E+I*(k:ℂ)*Real.pi
  let G := fun E => hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E
  have hP := (analyticOnNhd_hillL2RealCutPrimitive q hq hr).continuousOn.mono
    (hillRealGapContour_sphere_subset q hq hr k hk)
  have hroot := (Complex.continuous_sinh.comp_continuousOn hP).const_mul 2
  have hG : ContinuousOn G (sphere (hillRealGapCenter q hq hr k:ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :=
    ((analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn).continuousOn.mono (subset_univ _)).div hroot
      (fun E hE => hillL2RealCutRoot_ne_zero q hq hr E (hillRealGapContour_sphere_subset q hq hr k hk hE))
  have hshift := shifted_frequency_period F G (hillRealGapCenter q hq hr k:ℂ) (I*(k:ℂ)*Real.pi)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le)
    (hP.add continuousOn_const) hG 3
  have h1 := hillPhysicalFrequencyMoment_odd_eq_zero q hq hr n hn k hk 0
  have h3 := hillPhysicalFrequencyMoment_odd_eq_zero q hq hr n hn k hk 1
  change hillPhysicalFrequencyMoment q hq hr n hn k 1=0 at h1
  change hillPhysicalFrequencyMoment q hq hr n hn k 3=0 at h3
  have he : (fun E => (F E-I*(k:ℂ)*Real.pi)^3*G E) =
      (fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3 *
        hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E) := by
    funext E
    dsimp only [F,G]
    ring
  rw [he] at hshift
  change _ = ∑ m ∈ Finset.range (3+1), (Nat.choose 3 m:ℂ)*(-(I*(k:ℂ)*Real.pi))^(3-m)*
    hillPhysicalFrequencyMoment q hq hr n hn k m at hshift
  rw [hshift]
  norm_num [Finset.sum_range_succ,h1,h3]
  ring

/-- The free coefficient and the second-moment coefficient have their
physical energy normalization. No full frequency formula is assumed. -/
theorem hillPhysicalCubicPhase_eq_free_and_secondMoment
    (n : ℕ) (hn : 1≤n) (k : ℕ) (hk : 1≤k) :
    (4:ℂ)*(Real.pi*I:ℂ)⁻¹ *
      (∮ E in C((hillRealGapCenter q hq hr k:ℂ),
        hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3 *
          hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E) =
      (8*(Real.pi:ℂ)^3*(k:ℂ)^3)*(if k=n then 1 else 0) -
        12*(k:ℂ)*hillPhysicalFrequencyMoment q hq hr n hn k 2 := by
  rw [hillPhysicalCubicPeriod_eq_secondMoment q hq hr n hn k hk,
    hillPhysicalFrequencyMoment_zero q hq hr n hn k hk]
  have hpi : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  simp [I_sq]
  split_ifs <;> ring

/-- An actual physical coordinate rotates by the free Kronecker term
and the raw second moment along the actual quartic gap tangent. -/
theorem fderiv_hillDirichletAbelianCoordinate_extension_quarticGapDirection
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1≤n) (k : ℕ) (hk : 1≤k) (C : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩:RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q))
      (hillQuarticContourDirection (⟨q,hq,hr⟩:RealPeriodOneHillPotential)
        (hillRealGapCenter q hq hr k:ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) =
      I*((8*(Real.pi:ℂ)^3*(k:ℂ)^3)*(if k=n then 1 else 0) -
        12*(k:ℂ)*hillPhysicalFrequencyMoment q hq hr n hn k 2)*
          hillDirichletAbelianCoordinate q hq hr n hn := by
  have hh := fderiv_hillDirichletAbelianCoordinate_extension_quarticContourDirection
    (⟨q,hq,hr⟩:RealPeriodOneHillPotential) h0q h0r
    (hillRealGapCenter q hq hr k:ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le)
    (hillRealGapContour_sphere_subset q hq hr k hk) n hn C hC hmatch
  rw [hillPhysicalCubicPhase_eq_free_and_secondMoment q hq hr n hn k hk] at hh
  exact hh

end NLS.KdV
