import NLS.KdV.HillDirichletVelocityTerminalFactor
import NLS.KdV.HillSummedRegularCorrectionAnalytic

/-! # Actual Abelian coordinates analytic through every closed own gap -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- Every actual scalar amplitude-weighted Abelian coordinate has a
genuine complex L2 analytic extension, even when its own gap is closed.
The closed-gap actual Dirichlet velocity derivative vanishes for every complex trace energy. -/
theorem exists_hillDirichletAbelianCoordinate_velocity_extension
    (n : ℕ) (hn : 1≤n) :
    ∃ Z : Coeff 2 → ℂ, AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q) ∧
      Z (SpectralWeight.one.toCoeff q)=hillDirichletAbelianCoordinate q hq hr n hn ∧
      (hillRealGapHalfLength q hq hr n=0 → ∀ (V : Coeff 2) (K : ℂ),
        HillDirichletVelocityData (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) n hn V K →
        (fderiv ℂ Z (SpectralWeight.one.toCoeff q))
          V=0) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        Z (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn := by
  obtain ⟨T,hT,hT0,hDT,hTmatch⟩ :=
    exists_hillDirichletAbelianTerminalFactor_velocity_extension q hq hr n hn
  obtain ⟨F,hF,hFmatch⟩ :=
    exists_hillSummedRegularAbelianCorrection_analytic_extension h0q h0r q hq hr n hn
  let K := hillLocalAbelianAmplitudePrefactor q hq hr n
  have hK : AnalyticAt ℂ K (SpectralWeight.one.toCoeff q) :=
    analyticAt_hillLocalAbelianAmplitudePrefactor q hq hr n hn
  let M : Coeff 2 → ℂ := fun p => K p*exp (I*F p)
  have hM : AnalyticAt ℂ M (SpectralWeight.one.toCoeff q) := hK.mul ((analyticAt_const.mul hF).cexp)
  let Z : Coeff 2 → ℂ := fun p => T p*M p
  have hZ : AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q) := hT.mul hM
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      Z (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn := by
    filter_upwards [hTmatch,hFmatch,hillLocalAbelianAmplitudePrefactor_eventually_eq_physical q hq hr n hn] with p hpT hpF hpK
    dsimp only [Z,M,K]
    rw [hpT,hpF,hpK,hillDirichletAbelianCoordinate_eq_factor p.val p.property.1 p.property.2 n hn]
    ring
  refine ⟨Z,hZ,hmatch.self_of_nhds,?_,hmatch⟩
  intro hc V K hv
  have hTZ : T (SpectralWeight.one.toCoeff q)=0 :=
    hT0.trans (hillDirichletAbelianTerminalFactor_closed q hq hr n hn hc)
  have hDZ := (hT.differentiableAt.hasFDerivAt.fun_mul hM.differentiableAt.hasFDerivAt).fderiv
  change fderiv ℂ Z (SpectralWeight.one.toCoeff q)=_ at hDZ
  rw [hDZ]
  change T (SpectralWeight.one.toCoeff q)*((fderiv ℂ M _) _)+
    M (SpectralWeight.one.toCoeff q)*((fderiv ℂ T _) _)=0
  rw [hTZ,hDT hc V K hv,zero_mul,mul_zero,add_zero]

/-- Every differentiable extension agreeing with the physical coordinate
near a closed gap has the same zero actual Dirichlet velocity derivative there. -/
theorem fderiv_hillDirichletAbelianCoordinate_closed_velocity_extension_eq_zero
    (n : ℕ) (hn : 1≤n) (hc : hillRealGapHalfLength q hq hr n=0)
    (C : Coeff 2 → ℂ) (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn)
    (V : Coeff 2) (K : ℂ)
    (hv : HillDirichletVelocityData (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) n hn V K) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q))
      V=0 := by
  obtain ⟨Z,hZ,_hZ0,hDZ,hZmatch⟩ :=
    exists_hillDirichletAbelianCoordinate_velocity_extension q hq hr h0q h0r n hn
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=Z (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch,hZmatch] with p hp hpZ
    exact hp.trans hpZ.symm
  rw [fderiv_eq_on_parity_of_eventuallyEq_realPotentials q hq hr C Z hC hZ.differentiableAt heq _
    hv.parity]
  exact hDZ hc V K hv

end NLS.KdV
