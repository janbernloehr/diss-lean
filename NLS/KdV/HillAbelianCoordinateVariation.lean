import NLS.KdV.HillActionSourceVariation
import NLS.KdV.HillAbelianCoordinateAnalytic

/-! # Actual Abelian coordinate variation at open and closed gaps

Actual action stationarity and the phase variation give a single trace
variation law for every physical coordinate, including its zero at a
closed gap. Nearby-real matching makes the law independent of the chosen
complex analytic extension. Normalized contour directions act diagonally.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

private theorem exists_open_coordinate_variation
    (n : ℕ) (hn : 1≤n) (ho : hillRealGapHalfLength q hq hr n≠0) :
    ∃ Z : Coeff 2 → ℂ, AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q) ∧
      (∀ b : ℂ, (fderiv ℂ Z (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=
          (-I*hillAbelianSelectedGlobalPsi q hq hr n hn b/2)*hillDirichletAbelianCoordinate q hq hr n hn) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        Z (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn := by
  let J := hillLocalContourAction q hq hr n
  have hJ := analyticAt_hillLocalContourAction q hq hr n hn
  have hJmatch := hillLocalContourAction_eventually_eq_physical q hq hr n hn
  have hJ0 : J (SpectralWeight.one.toCoeff q)=(hillRealGapIntegral q hq hr n 0:ℂ) := hJmatch.self_of_nhds
  have hI : 0<hillRealGapIntegral q hq hr n 0 := by
    apply (hillRealGapIntegral_pos_iff q hq hr n hn).mpr
    have hle := monotone_hillRealLabels q hq hr (show 2*n-1≤2*n by omega)
    apply lt_of_le_of_ne hle
    intro he
    apply ho
    simp only [hillRealGapHalfLength,he,sub_self,zero_div]
  have hslit : J (SpectralWeight.one.toCoeff q)∈Complex.slitPlane := by
    rw [hJ0,Complex.mem_slitPlane_iff]
    exact Or.inl (by simpa only [ofReal_re] using hI)
  let K : Coeff 2 → ℂ := fun p => Complex.sqrt (J p)
  have hsqrt := Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hslit)
  have hK : AnalyticAt ℂ K (SpectralWeight.one.toCoeff q) := hsqrt.comp hJ
  have hKmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      K (SpectralWeight.one.toCoeff p.val)=(Real.sqrt (hillRealGapIntegral p.val p.property.1 p.property.2 n 0):ℂ) := by
    filter_upwards [hJmatch] with p hp
    dsimp only [K,J]
    rw [hp,Complex.sqrt_of_nonneg (by exact_mod_cast
      (show 0≤hillRealGapIntegral p.val p.property.1 p.property.2 n 0 from by
        simpa only [mul_zero] using hillRealGapIntegral_nonneg_even p.val p.property.1 p.property.2 n hn 0)),ofReal_re]
  have hKzero (b : ℂ) : (fderiv ℂ K (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
    have hd := (hsqrt.differentiableAt.hasFDerivAt.comp (SpectralWeight.one.toCoeff q) hJ.differentiableAt.hasFDerivAt).fderiv
    change fderiv ℂ K (SpectralWeight.one.toCoeff q)=_ at hd
    rw [hd,ContinuousLinearMap.comp_apply,fderiv_hillLocalContourAction_gardnerDirection_eq_zero q hq hr n hn,map_zero]
  obtain ⟨P,hP,_hP0,hDP,_hperiod,hPmatch⟩ :=
    exists_hillDirichletAbelianPhase_analytic_variation q hq hr h0q h0r n hn ho
  let Z : Coeff 2 → ℂ := fun p => K p*P p
  have hZ : AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q) := hK.mul hP
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      Z (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn := by
    filter_upwards [hKmatch,hPmatch] with p hpK hpP
    exact congrArg₂ (fun a b : ℂ => a*b) hpK hpP.2
  refine ⟨Z,hZ,?_,hmatch⟩
  intro b
  have hd := (hK.differentiableAt.hasFDerivAt.fun_mul hP.differentiableAt.hasFDerivAt).fderiv
  change fderiv ℂ Z (SpectralWeight.one.toCoeff q)=_ at hd
  rw [hd]
  change K (SpectralWeight.one.toCoeff q)*((fderiv ℂ P _) _)+P (SpectralWeight.one.toCoeff q)*((fderiv ℂ K _) _)=_
  rw [hDP b,hKzero b,mul_zero,add_zero,hKmatch.self_of_nhds]
  dsimp only [hillDirichletAbelianCoordinate]
  ring

/-- Every differentiable extension of an actual physical coordinate obeys
the same Gardner trace law at all gaps, including a closed selected gap. -/
theorem fderiv_hillDirichletAbelianCoordinate_extension
    (n : ℕ) (hn : 1≤n) (C : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn)
    (b : ℂ) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=
        (-I*hillAbelianSelectedGlobalPsi q hq hr n hn b/2)*hillDirichletAbelianCoordinate q hq hr n hn := by
  by_cases hc : hillRealGapHalfLength q hq hr n=0
  · rw [fderiv_hillDirichletAbelianCoordinate_closed_extension_eq_zero q hq hr h0q h0r n hn hc C hC hmatch b,
      hillDirichletAbelianCoordinate_closed q hq hr n hn hc,mul_zero]
  · obtain ⟨Z,hZ,hDZ,hZmatch⟩ := exists_open_coordinate_variation q hq hr h0q h0r n hn hc
    have he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        C (SpectralWeight.one.toCoeff p.val)=Z (SpectralWeight.one.toCoeff p.val) := by
      filter_upwards [hmatch,hZmatch] with p hp hpZ
      exact hp.trans hpZ.symm
    rw [fderiv_eq_on_parity_of_eventuallyEq_realPotentials q hq hr C Z hC hZ.differentiableAt he _
      (hillL2DiscriminantGardnerDirection_mem_parity _ b)]
    exact hDZ b

/-- Normalized physical contour directions act as diagonal infinitesimal
rotations of every actual coordinate, at arbitrary closed-gap sources. -/
theorem fderiv_hillDirichletAbelianCoordinate_extension_tracePeriodDirection
    (n m : ℕ) (hn : 1≤n) (hm : 1≤m) (C : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q)) (hillL2TracePeriodDirection q hq hr m)=
      I*(if m=n then 1 else 0)*hillDirichletAbelianCoordinate q hq hr n hn := by
  rw [apply_hillL2TracePeriodDirection q hq hr m hm]
  have he : (fun E => (fderiv ℂ C (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) E)/hillEnergyCanonicalRootProduct q hq hr E)=
      (fun E => (-I/2*hillDirichletAbelianCoordinate q hq hr n hn)*
        (hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E)) := by
    funext E
    rw [fderiv_hillDirichletAbelianCoordinate_extension q hq hr h0q h0r n hn C hC hmatch E]
    ring
  rw [he,circleIntegral.integral_const_mul]
  have hp := hillAbelianSelectedGlobalPsi_intrinsic_periods q hq hr n hn m hm
  have heq : -(Real.pi : ℂ)⁻¹*((-I/2*hillDirichletAbelianCoordinate q hq hr n hn)*
      (∮ E in C((hillRealGapCenter q hq hr m : ℂ),hillRealGapHalfLength q hq hr m+hillRealGapCollar q hq hr m),
        hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E))=
      I*((2*(Real.pi : ℂ))⁻¹*(∮ E in C((hillRealGapCenter q hq hr m : ℂ),hillRealGapHalfLength q hq hr m+hillRealGapCollar q hq hr m),
        hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E))*hillDirichletAbelianCoordinate q hq hr n hn := by ring
  rw [heq,hp]

end NLS.KdV
