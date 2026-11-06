import NLS.KdV.HillGardnerSummedCorrection

/-! # Local physical Abelian angle and its Gardner derivative -/
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

/-- The local raw Abelian angle is the own-gap terminal angle minus pi plus
the actual absolutely convergent regular correction sum. It is analytic
in a complex L2 neighborhood and has the exact Gardner derivative. This
statement does not identify its sign with a canonical Birkhoff angle. -/
theorem exists_hillDirichletAbelianAngle_gardner_variation
    (n : ℕ) (hn : 1≤n) (hnopen : hillRealGapHalfLength q hq hr n≠0) :
    ∃ A ε : Coeff 2 → ℂ, ∃ e : ℂ,
      AnalyticAt ℂ A (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q) ∧
      ε (SpectralWeight.one.toCoeff q)=e ∧ e∈segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ∧
      (∀ b : ℂ, (fderiv ℂ A (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=
          -hillAbelianSelectedGlobalPsi q hq hr n hn b/2) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im=0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 n)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 n) (ε (SpectralWeight.one.toCoeff p.val))=
            (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 n hn ∧
        A (SpectralWeight.one.toCoeff p.val)=ε (SpectralWeight.one.toCoeff p.val)-(Real.pi:ℂ)+
          hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n hn ∧
        (A (SpectralWeight.one.toCoeff p.val)).im=0 := by
  obtain ⟨F,hF,hDF,hFmatch⟩ :=
    exists_hillSummedRegularAbelianCorrection_gardner_variation h0q h0r q hq hr n hn hnopen
  obtain ⟨B,ε,e,_hB,hε,hε0,he,_hDB,hphysical⟩ :=
    exists_hillDirichletAbelianIntegral_gardner_variation q hq hr h0q h0r n n hn hn hnopen
  let A : Coeff 2 → ℂ := fun p => ε p-(Real.pi:ℂ)+F p
  have hA : AnalyticAt ℂ A (SpectralWeight.one.toCoeff q) := (hε.sub analyticAt_const).add hF
  have hterminal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 n)
        (hillRealGapHalfLength p.val p.property.1 p.property.2 n) (ε (SpectralWeight.one.toCoeff p.val))=
          (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) ∧
      Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 n hn :=
    hphysical.mono (fun _ hp => ⟨hp.2.2.1,hp.2.2.2.1⟩)
  refine ⟨A,ε,e,hA,hε,hε0,he,?_,?_⟩
  · intro b
    have hDA : fderiv ℂ A (SpectralWeight.one.toCoeff q) =
        fderiv ℂ ε (SpectralWeight.one.toCoeff q)+fderiv ℂ F (SpectralWeight.one.toCoeff q) :=
      ((hε.differentiableAt.hasFDerivAt.sub_const (Real.pi:ℂ)).add hF.differentiableAt.hasFDerivAt).fderiv
    rw [hDA]
    change (fderiv ℂ ε _) _+(fderiv ℂ F _) _ = _
    rw [hDF b,fderiv_hillDirichletTerminalAngle_gardnerDirection (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)
      n hn hnopen ε hε.differentiableAt hterminal b]
    ring
  · filter_upwards [hphysical,hFmatch] with p hp hpF
    refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,?_,?_⟩
    · dsimp only [A]
      rw [hpF]
    · dsimp only [A]
      rw [hpF]
      simp only [add_im,sub_im,hp.2.1,ofReal_im,sub_self,zero_add,
        hillSummedRegularAbelianCorrection_im_eq_zero h0q h0r p.val p.property.1 p.property.2 n hn]

end NLS.KdV
