import NLS.KdV.HillSignedAbelianAnalytic

/-! # Physical action differentials and the collapsed-gap locus

The actual action is the product of its positive and negative physical
coordinates. Matching complex extensions therefore determine its full
period-one differential. In particular a collapsed action has zero
physical differential, and its actual Gardner Hamiltonian vector vanishes
precisely at that collapsed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The product rule for the actual action, on every physical complex
period-one tangent, independently of the matching extensions chosen. -/
theorem fderiv_hillRealAction_eq_coordinate_product
    (n : ℕ) (hn : 1≤n) (A Z W : Coeff 2 → ℂ)
    (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff q))
    (hZ : DifferentiableAt ℂ Z (SpectralWeight.one.toCoeff q))
    (hW : DifferentiableAt ℂ W (SpectralWeight.one.toCoeff q))
    (hAmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ))
    (hZmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      Z (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn)
    (hWmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      W (SpectralWeight.one.toCoeff p.val)=conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn))
    (v : Coeff 2) (hv : v∈Coeff.paritySubspace 0) :
    (fderiv ℂ A (SpectralWeight.one.toCoeff q)) v=
      hillDirichletAbelianCoordinate q hq hr n hn*((fderiv ℂ W (SpectralWeight.one.toCoeff q)) v)+
      conj (hillDirichletAbelianCoordinate q hq hr n hn)*((fderiv ℂ Z (SpectralWeight.one.toCoeff q)) v) := by
  have hprod : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=
        Z (SpectralWeight.one.toCoeff p.val)*W (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hAmatch,hZmatch,hWmatch] with p hpA hpZ hpW
    rw [hpA,hpZ,hpW,mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,
      norm_sq_hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 h0q h0r n hn]
  rw [fderiv_eq_on_parity_of_eventuallyEq_realPotentials q hq hr A (fun p => Z p*W p)
    hA (hZ.mul hW) hprod v hv,(hZ.hasFDerivAt.fun_mul hW.hasFDerivAt).fderiv]
  change Z _*((fderiv ℂ W _) v)+W _*((fderiv ℂ Z _) v)=_
  rw [hZmatch.self_of_nhds,hWmatch.self_of_nhds]

/-- At a closed selected gap, the actual action differential vanishes on
the entire physical period-one complex tangent space. -/
theorem fderiv_hillRealAction_closed_eq_zero
    (n : ℕ) (hn : 1≤n) (hc : hillRealGapHalfLength q hq hr n=0)
    (A : Coeff 2 → ℂ) (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ))
    (v : Coeff 2) (hv : v∈Coeff.paritySubspace 0) :
    (fderiv ℂ A (SpectralWeight.one.toCoeff q)) v=0 := by
  obtain ⟨Z,hZ,_hZ0,_hclosed,hZmatch⟩ :=
    exists_hillDirichletAbelianCoordinate_analytic_extension q hq hr h0q h0r n hn
  obtain ⟨W,hW,_hW0,hWmatch⟩ :=
    exists_hillNegativeAbelianCoordinate_analytic_extension q hq hr h0q h0r n hn
  rw [fderiv_hillRealAction_eq_coordinate_product q hq hr h0q h0r n hn A Z W hA
    hZ.differentiableAt hW.differentiableAt hmatch hZmatch hWmatch v hv,
    hillDirichletAbelianCoordinate_closed q hq hr n hn hc,map_zero,zero_mul,zero_mul,add_zero]

/-- Every physical action Hamiltonian vector vanishes at its collapsed gap. -/
theorem IsHillHamiltonianDirection.eq_zero_of_action_closed
    (n : ℕ) (hn : 1≤n) (hc : hillRealGapHalfLength q hq hr n=0)
    (A : Coeff 2 → ℂ) (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ))
    (v : Coeff 2) (hv : IsHillHamiltonianDirection (SpectralWeight.one.toCoeff q) A v) : v=0 := by
  apply hv.unique
  refine ⟨(Coeff.paritySubspace 0).zero_mem,rfl,?_⟩
  intro f g _hf _hfg _hfe _hge
  rw [map_zero,fderiv_hillRealAction_closed_eq_zero q hq hr h0q h0r n hn hc A hA hmatch _
    (Coeff.periodDouble_mem _),neg_zero]

/-- The literal normalized action contour vector has exactly the closed
gap as its zero locus; no gap-opening or flow hypothesis is supplied. -/
theorem hillL2TracePeriodDirection_eq_zero_iff_closed (n : ℕ) (hn : 1≤n) :
    hillL2TracePeriodDirection q hq hr n=0 ↔ hillRealGapHalfLength q hq hr n=0 := by
  constructor
  · intro hY
    obtain ⟨Z,hZ,_hZ0,_hclosed,hZmatch⟩ :=
      exists_hillDirichletAbelianCoordinate_analytic_extension q hq hr h0q h0r n hn
    have hd := fderiv_hillDirichletAbelianCoordinate_extension_tracePeriodDirection
      q hq hr h0q h0r n n hn hn Z hZ.differentiableAt hZmatch
    rw [hY,map_zero,if_pos rfl, mul_one] at hd
    have hz : hillDirichletAbelianCoordinate q hq hr n hn=0 :=
      (mul_eq_zero.mp hd.symm).resolve_left I_ne_zero
    exact (hillDirichletAbelianCoordinate_eq_zero_iff q hq hr h0q h0r n hn).mp hz
  · intro hc
    exact IsHillHamiltonianDirection.eq_zero_of_action_closed q hq hr h0q h0r n hn hc
      (hillLocalContourAction q hq hr n) (analyticAt_hillLocalContourAction q hq hr n hn).differentiableAt
      (hillLocalContourAction_eventually_eq_physical q hq hr n hn) _
      (hillL2TracePeriodDirection_is_action_hamiltonian q hq hr n hn _
        (analyticAt_hillLocalContourAction q hq hr n hn).differentiableAt
        (hillLocalContourAction_eventually_eq_physical q hq hr n hn))

/-- The critical locus of the actual action on its full complexified
physical tangent space is precisely its closed-gap locus. -/
theorem fderiv_hillRealAction_vanishes_iff_closed
    (n : ℕ) (hn : 1≤n) (A : Coeff 2 → ℂ)
    (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ)) :
    (∀ v : Coeff 2, v∈Coeff.paritySubspace 0 →
      (fderiv ℂ A (SpectralWeight.one.toCoeff q)) v=0) ↔ hillRealGapHalfLength q hq hr n=0 := by
  constructor
  · intro hd
    have hz : IsHillHamiltonianDirection (SpectralWeight.one.toCoeff q) A 0 := by
      refine ⟨(Coeff.paritySubspace 0).zero_mem,rfl,?_⟩
      intro f g _hf _hfg _hfe _hge
      rw [map_zero,hd _ (Coeff.periodDouble_mem _),neg_zero]
    have hY := (hillL2TracePeriodDirection_is_action_hamiltonian q hq hr n hn A hA hmatch).unique hz
    exact (hillL2TracePeriodDirection_eq_zero_iff_closed q hq hr h0q h0r n hn).mp hY
  · intro hc v hv
    exact fderiv_hillRealAction_closed_eq_zero q hq hr h0q h0r n hn hc A hA hmatch v hv

end NLS.KdV
