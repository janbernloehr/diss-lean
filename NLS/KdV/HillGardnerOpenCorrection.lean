import NLS.KdV.HillGardnerClosedCorrection

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
theorem fderiv_hillRegularAbelianCorrection_open_extension
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength q hq hr k ≠ 0)
    (C : Coeff 2 → ℂ) (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val) = hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk)
    (b : ℂ) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b) =
      hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr k hk) *
        hillDirichletGardnerKernel (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk b -
      (if k=n then 1 else 0) *
        (I * hillDeflatedEnergyCanonicalRoot q hq hr k (hillDirichletEnergy q hq hr k hk) *
          hillDirichletGardnerKernel (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk b) := by
  obtain ⟨B,ε,e,hB,hε,_,_,hDB,hphysical⟩ :=
    exists_hillDirichletAbelianIntegral_gardner_variation q hq hr h0q h0r n k hn hk hgap
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
    (hillL2DiscriminantGardnerDirection_mem_parity _ b)]
  have hterminal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
        (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (SpectralWeight.one.toCoeff p.val)) =
          (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
      Complex.sin (ε (SpectralWeight.one.toCoeff p.val)) = hillDirichletGapSine p.val p.property.1 p.property.2 k hk :=
    hphysical.mono (fun _ hp => ⟨hp.2.2.1,hp.2.2.2.1⟩)
  have hDε := fderiv_hillDirichletTerminalAngle_gardnerDirection (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)
    k hk hgap ε hε.differentiableAt hterminal b
  have hDL : fderiv ℂ L (SpectralWeight.one.toCoeff q) =
      fderiv ℂ B (SpectralWeight.one.toCoeff q) -
        (if k=n then (1:ℂ) else 0) • fderiv ℂ ε (SpectralWeight.one.toCoeff q) :=
    (hB.differentiableAt.hasFDerivAt.sub
      ((hε.differentiableAt.hasFDerivAt.sub_const (Real.pi:ℂ)).const_mul (if k=n then 1 else 0))).fderiv
  rw [hDL]
  change (fderiv ℂ B _) _ - (if k=n then 1 else 0)*((fderiv ℂ ε _) _) = _
  rw [hDB b,hDε]

omit h0q h0r in
/-- At a collapsed gap, every normalized numerator except the omitted
own-gap numerator vanishes at the actual Dirichlet energy. -/
theorem hillAbelianSelectedGlobalPsi_dirichlet_eq_zero_of_closed
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hkn : k≠n)
    (hc : hillRealGapHalfLength q hq hr k=0) :
    hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr k hk)=0 := by
  have hab : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k) := by
    dsimp only [hillRealGapHalfLength] at hc
    linarith
  have hμ := hillDirichletEnergy_mem_gap q hq hr k hk
  have hroot := (hillAbelianSelectedGlobalRoots q hq hr n hn).property (k-1)
  change _ ∈ Icc _ _ at hroot
  have hidx : k-1+1=k := by omega
  rw [hidx] at hroot
  apply (hillAbelianSelectedGlobalPsi_zero_iff q hq hr n hn _).2
  refine ⟨k-1,by simpa only [hidx] using hkn,?_⟩
  have he : (hillAbelianSelectedGlobalRoots q hq hr n hn).val (k-1)=hillDirichletEnergy q hq hr k hk := by
    linarith [hroot.1,hroot.2,hμ.1,hμ.2]
  exact congrArg (fun x : ℝ => (x:ℂ)) he

/-- Uniform per-index formula for the actual regular correction when the
selected angle gap is open. The index being summed may be open or closed. -/
theorem fderiv_hillRegularAbelianCorrection_extension
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hnopen : hillRealGapHalfLength q hq hr n≠0)
    (C : Coeff 2 → ℂ) (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk)
    (b : ℂ) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b) =
      hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr k hk)*
        hillDirichletGardnerKernel (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk b -
      (if k=n then 1 else 0)*
        (I*hillDeflatedEnergyCanonicalRoot q hq hr n (hillDirichletEnergy q hq hr n hn)*
          hillDirichletGardnerKernel (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) n hn b) := by
  by_cases hc : hillRealGapHalfLength q hq hr k=0
  · have hkn : k≠n := by intro h;subst k;exact hnopen hc
    rw [fderiv_hillRegularAbelianCorrection_closed_extension_eq_zero q hq hr h0q h0r n k hn hk hc C hC hmatch b,
      hillAbelianSelectedGlobalPsi_dirichlet_eq_zero_of_closed q hq hr n k hn hk hkn hc,
      if_neg hkn,zero_mul,zero_mul,sub_zero]
  · rw [fderiv_hillRegularAbelianCorrection_open_extension q hq hr h0q h0r n k hn hk hc C hC hmatch b]
    by_cases hkn : k=n
    · subst k; rfl
    · simp only [if_neg hkn,zero_mul]

end NLS.KdV
