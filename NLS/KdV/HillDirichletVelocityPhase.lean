import NLS.KdV.HillAbelianPhase
import NLS.KdV.HillDirichletVelocityAbelianAngle

/-! # Actual physical phase derivatives from the convergent Dirichlet series -/
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

/-- The actual branch-independent phase has a genuine local analytic
extension whose derivative is given by the actual convergent Dirichlet
series multiplied by its physical unit phase. -/
theorem exists_hillDirichletAbelianPhase_velocity_variation
    (n : ℕ) (hn : 1≤n) (hnopen : hillRealGapHalfLength q hq hr n≠0) :
    ∃ P : Coeff 2 → ℂ, AnalyticAt ℂ P (SpectralWeight.one.toCoeff q) ∧
      P (SpectralWeight.one.toCoeff q)=hillDirichletAbelianPhase q hq hr n hn ∧
      (∀ (V : Coeff 2) (K : ℕ → ℂ),
        (∀ (k : ℕ) (hk : 1≤k), HillDirichletVelocityData (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk V (K k)) →
        Tendsto (fun M : ℕ => (∑ j ∈ Finset.range M,
          hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))*K (j+1))*
            (I*hillDirichletAbelianPhase q hq hr n hn))
          atTop (𝓝 ((fderiv ℂ P (SpectralWeight.one.toCoeff q)) V))) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 ∧
        P (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianPhase p.val p.property.1 p.property.2 n hn := by
  obtain ⟨A,ε,e,hA,_hε,_hε0,_he,hDA,hphysical⟩ :=
    exists_hillDirichletAbelianAngle_velocity_variation q hq hr h0q h0r n hn hnopen
  let P : Coeff 2 → ℂ := fun p => exp (I*A p)
  have hP : AnalyticAt ℂ P (SpectralWeight.one.toCoeff q) := (analyticAt_const.mul hA).cexp
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 ∧
      P (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianPhase p.val p.property.1 p.property.2 n hn := by
    filter_upwards [hphysical] with p hp
    refine ⟨hp.1,?_⟩
    dsimp only [P]
    rw [hp.2.2.2.2.1]
    exact (hillDirichletAbelianPhase_eq_exp_terminal p.val p.property.1 p.property.2 n hn hp.1 _ hp.2.2.1 hp.2.2.2.1).symm
  have hP0 := (hmatch.self_of_nhds).2
  have hDP : fderiv ℂ P (SpectralWeight.one.toCoeff q)=
      P (SpectralWeight.one.toCoeff q) • (I • fderiv ℂ A (SpectralWeight.one.toCoeff q)) :=
    (hA.differentiableAt.hasFDerivAt.const_mul I).cexp.fderiv
  refine ⟨P,hP,hP0,?_,hmatch⟩
  intro V K hv
  have he : ((fderiv ℂ A (SpectralWeight.one.toCoeff q)) V)*
      (I*hillDirichletAbelianPhase q hq hr n hn)=((fderiv ℂ P (SpectralWeight.one.toCoeff q)) V) := by
    rw [hDP]
    change _=P (SpectralWeight.one.toCoeff q)*(I*((fderiv ℂ A _) V))
    rw [hP0]
    ring
  simpa only [he] using (hDA V K hv).mul_const (I*hillDirichletAbelianPhase q hq hr n hn)

end NLS.KdV
