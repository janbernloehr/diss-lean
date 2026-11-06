import NLS.KdV.HillGardnerClosedCorrection
import NLS.KdV.HillDirichletVelocityAbelianIntegral

/-! # Actual regular Abelian correction variations at open gaps -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The actual regular correction has the normalized-numerator terminal
variation, with the own-gap elementary angle contribution removed. The
identity holds for every differentiable extension with real physical
matching, including terminal bandedges and the filled spectral diagonal. -/
theorem fderiv_hillRegularAbelianCorrection_open_velocity_extension
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength q hq hr k ≠ 0)
    (C : Coeff 2 → ℂ) (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val) = hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk)
    (V : Coeff 2) (K : ℂ)
    (hv : HillDirichletVelocityData (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk V K) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q))
      V =
      hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr k hk) *
        K -
      (if k=n then 1 else 0) *
        (I * hillDeflatedEnergyCanonicalRoot q hq hr k (hillDirichletEnergy q hq hr k hk) *
          K) := by
  obtain ⟨B,ε,e,hB,hε,_,_,hDB,hphysical⟩ :=
    exists_hillDirichletAbelianIntegral_velocity_variation q hq hr h0q h0r n k hn hk hgap
  let L : Coeff 2 → ℂ := fun p => B p-(if k=n then 1 else 0)*(ε p-(Real.pi:ℂ))
  have hL : AnalyticAt ℂ L (SpectralWeight.one.toCoeff q) :=
    hB.sub (analyticAt_const.mul (hε.sub analyticAt_const))
  have hLmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      L (SpectralWeight.one.toCoeff p.val) = hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk := by
    filter_upwards [hphysical] with p hp
    let P := SpectralWeight.one.toCoeff p.val
    have hreal : ε P = ((ε P).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [ofReal_im] using (show (ε P).im = 0 from hp.2.1)
    have hpoint := hp.2.2.1
    have hsin := hp.2.2.2.1
    change cosineGapPoint _ _ (ε P) = _ at hpoint
    change Complex.sin (ε P) = _ at hsin
    rw [hreal] at hpoint hsin
    rw [hillRegularAbelianCorrection_eq_of_terminal p.val p.property.1 p.property.2 n k hn hk hp.1 _ hpoint hsin]
    change B P-(if k=n then 1 else 0)*(ε P-(Real.pi:ℂ)) = _
    rw [hp.2.2.2.2.1]
    change hillRegularAbelianPrimitive p.val p.property.1 p.property.2 n hn k (ε P) =
      hillRegularAbelianPrimitive p.val p.property.1 p.property.2 n hn k ((ε P).re : ℂ)
    rw [hreal]
    simp only [ofReal_re]
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val) = L (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch,hLmatch] with p hp hpL
    exact hp.trans hpL.symm
  rw [fderiv_eq_on_parity_of_eventuallyEq_realPotentials q hq hr C L hC hL.differentiableAt heq _
    hv.parity]
  have hterminal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
        (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (SpectralWeight.one.toCoeff p.val)) =
          (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
      Complex.sin (ε (SpectralWeight.one.toCoeff p.val)) = hillDirichletGapSine p.val p.property.1 p.property.2 k hk :=
    hphysical.mono (fun _ hp => ⟨hp.2.2.1,hp.2.2.2.1⟩)
  have hDε := HillDirichletVelocityData.terminal_angle (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)
    k hk hgap ε hε.differentiableAt hterminal V K hv
  have hDL : fderiv ℂ L (SpectralWeight.one.toCoeff q) =
      fderiv ℂ B (SpectralWeight.one.toCoeff q) -
        (if k=n then (1:ℂ) else 0) • fderiv ℂ ε (SpectralWeight.one.toCoeff q) :=
    (hB.differentiableAt.hasFDerivAt.sub
      ((hε.differentiableAt.hasFDerivAt.sub_const (Real.pi:ℂ)).const_mul (if k=n then 1 else 0))).fderiv
  rw [hDL]
  change (fderiv ℂ B _) _ - (if k=n then 1 else 0)*((fderiv ℂ ε _) _) = _
  rw [hDB V K hv,hDε]

end NLS.KdV
