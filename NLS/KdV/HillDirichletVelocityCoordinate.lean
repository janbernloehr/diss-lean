import NLS.KdV.HillActionSourceVariation
import NLS.KdV.HillDirichletVelocityClosedCoordinate
import NLS.KdV.HillDirichletVelocityPhase

/-! # Actual Dirichlet-series coordinate variation at every gap

Actual action stationarity and the phase variation give a convergent
Dirichlet-series derivative for every physical coordinate. At a closed
own gap its derivative vanishes by the actual terminal-factor calculus.
Physical matching determines the derivative of every chosen extension.
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

private theorem exists_open_coordinate_velocity_variation
    (n : ℕ) (hn : 1≤n) (ho : hillRealGapHalfLength q hq hr n≠0) :
    ∃ Z : Coeff 2 → ℂ, AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q) ∧
      (∀ (V : Coeff 2) (K : ℕ → ℂ),
        (∀ (k : ℕ) (hk : 1≤k), HillDirichletVelocityData (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk V (K k)) →
        Tendsto (fun M : ℕ => (∑ j ∈ Finset.range M,
          hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))*K (j+1))*
            (I*hillDirichletAbelianCoordinate q hq hr n hn))
          atTop (𝓝 ((fderiv ℂ Z (SpectralWeight.one.toCoeff q)) V))) ∧
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
  have hKzero (V : Coeff 2)
      (hV : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (SpectralWeight.one.toCoeff q)) V=0) :
      (fderiv ℂ K (SpectralWeight.one.toCoeff q)) V=0 := by
    have hJzero : (fderiv ℂ J (SpectralWeight.one.toCoeff q)) V=0 := by
      rw [fderiv_hillLocalContourAction_apply q hq hr n hn]
      simp only [hV,zero_div]
      simp [circleIntegral]
    have hd := (hsqrt.differentiableAt.hasFDerivAt.comp (SpectralWeight.one.toCoeff q) hJ.differentiableAt.hasFDerivAt).fderiv
    change fderiv ℂ K (SpectralWeight.one.toCoeff q)=_ at hd
    rw [hd,ContinuousLinearMap.comp_apply,hJzero,map_zero]
  obtain ⟨P,hP,_hP0,hDP,hPmatch⟩ :=
    exists_hillDirichletAbelianPhase_velocity_variation q hq hr h0q h0r n hn ho
  let Z : Coeff 2 → ℂ := fun p => K p*P p
  have hZ : AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q) := hK.mul hP
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      Z (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn := by
    filter_upwards [hKmatch,hPmatch] with p hpK hpP
    exact congrArg₂ (fun a b : ℂ => a*b) hpK hpP.2
  refine ⟨Z,hZ,?_,hmatch⟩
  intro V F hv
  have hd := (hK.differentiableAt.hasFDerivAt.fun_mul hP.differentiableAt.hasFDerivAt).fderiv
  change fderiv ℂ Z (SpectralWeight.one.toCoeff q)=_ at hd
  have he : K (SpectralWeight.one.toCoeff q)*((fderiv ℂ P (SpectralWeight.one.toCoeff q)) V)=
      (fderiv ℂ Z (SpectralWeight.one.toCoeff q)) V := by
    rw [hd]
    change _=K (SpectralWeight.one.toCoeff q)*((fderiv ℂ P _) V)+P (SpectralWeight.one.toCoeff q)*((fderiv ℂ K _) V)
    rw [hKzero V (hv n hn).trace_stationary,mul_zero,add_zero]
  have hh := (hDP V F hv).const_mul (K (SpectralWeight.one.toCoeff q))
  rw [he] at hh
  apply hh.congr'
  exact Filter.Eventually.of_forall (fun M => by
    rw [hKmatch.self_of_nhds]
    dsimp only [hillDirichletAbelianCoordinate]
    ring)

/-- Every differentiable physical matching coordinate extension has its
actual Dirichlet-series velocity at all gaps, including a closed own gap. -/
theorem fderiv_hillDirichletAbelianCoordinate_velocity_extension
    (n : ℕ) (hn : 1≤n) (C : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn)
    (V : Coeff 2) (K : ℕ → ℂ)
    (hv : ∀ (k : ℕ) (hk : 1≤k), HillDirichletVelocityData (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk V (K k)) :
    Tendsto (fun M : ℕ => (∑ j ∈ Finset.range M,
      hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))*K (j+1))*
        (I*hillDirichletAbelianCoordinate q hq hr n hn))
      atTop (𝓝 ((fderiv ℂ C (SpectralWeight.one.toCoeff q)) V)) := by
  by_cases hc : hillRealGapHalfLength q hq hr n=0
  · rw [fderiv_hillDirichletAbelianCoordinate_closed_velocity_extension_eq_zero q hq hr h0q h0r n hn hc C hC hmatch V (K n) (hv n hn),
      hillDirichletAbelianCoordinate_closed q hq hr n hn hc]
    simpa only [mul_zero] using (tendsto_const_nhds (x := (0:ℂ)))
  · obtain ⟨Z,hZ,hDZ,hZmatch⟩ := exists_open_coordinate_velocity_variation q hq hr h0q h0r n hn hc
    have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        C (SpectralWeight.one.toCoeff p.val)=Z (SpectralWeight.one.toCoeff p.val) := by
      filter_upwards [hmatch,hZmatch] with p hp hpZ
      exact hp.trans hpZ.symm
    rw [fderiv_eq_on_parity_of_eventuallyEq_realPotentials q hq hr C Z hC hZ.differentiableAt heq V (hv n hn).parity]
    exact hDZ V K hv

end NLS.KdV
