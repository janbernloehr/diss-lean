import NLS.KdV.HillDirichletVelocitySummedCorrection

/-! # Local physical Abelian angle and its differentiated Dirichlet series -/
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
in a complex L2 neighborhood and has its source derivative given by the convergent actual Dirichlet series. This
statement does not identify its sign with a canonical Birkhoff angle. -/
theorem exists_hillDirichletAbelianAngle_velocity_variation
    (n : ℕ) (hn : 1≤n) (hnopen : hillRealGapHalfLength q hq hr n≠0) :
    ∃ A ε : Coeff 2 → ℂ, ∃ e : ℂ,
      AnalyticAt ℂ A (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q) ∧
      ε (SpectralWeight.one.toCoeff q)=e ∧ e∈segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ∧
      (∀ (V : Coeff 2) (K : ℕ → ℂ),
        (∀ (k : ℕ) (hk : 1≤k), HillDirichletVelocityData (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk V (K k)) →
        Tendsto (fun M : ℕ => ∑ j ∈ Finset.range M,
          hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))*K (j+1))
          atTop (𝓝 ((fderiv ℂ A (SpectralWeight.one.toCoeff q)) V))) ∧
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
    exists_hillSummedRegularAbelianCorrection_velocity_variation h0q h0r q hq hr n hn hnopen
  obtain ⟨B,ε,e,_hB,hε,hε0,he,_hDB,hphysical⟩ :=
    exists_hillDirichletAbelianIntegral_velocity_variation q hq hr h0q h0r n n hn hn hnopen
  let A : Coeff 2 → ℂ := fun p => ε p-(Real.pi:ℂ)+F p
  have hA : AnalyticAt ℂ A (SpectralWeight.one.toCoeff q) := (hε.sub analyticAt_const).add hF
  have hterminal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 n)
        (hillRealGapHalfLength p.val p.property.1 p.property.2 n) (ε (SpectralWeight.one.toCoeff p.val))=
          (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) ∧
      Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 n hn :=
    hphysical.mono (fun _ hp => ⟨hp.2.2.1,hp.2.2.2.1⟩)
  refine ⟨A,ε,e,hA,hε,hε0,he,?_,?_⟩
  · intro V K hv
    let Z := I*hillDeflatedEnergyCanonicalRoot q hq hr n (hillDirichletEnergy q hq hr n hn)*K n
    have hDA : fderiv ℂ A (SpectralWeight.one.toCoeff q) =
        fderiv ℂ ε (SpectralWeight.one.toCoeff q)+fderiv ℂ F (SpectralWeight.one.toCoeff q) :=
      ((hε.differentiableAt.hasFDerivAt.sub_const (Real.pi:ℂ)).add hF.differentiableAt.hasFDerivAt).fderiv
    have hDε : (fderiv ℂ ε (SpectralWeight.one.toCoeff q)) V=Z :=
      HillDirichletVelocityData.terminal_angle (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)
        n hn hnopen ε hε.differentiableAt hterminal V (K n) (hv n hn)
    have hsum (M : ℕ) (hM : n≤M) :
        ∑ j ∈ Finset.range M, (if j+1=n then (1:ℂ) else 0)*Z=Z := by
      have he (j : ℕ) : j+1=n ↔ j=n-1 := by omega
      simp_rw [ite_mul,one_mul,zero_mul,he]
      simp only [Finset.sum_ite_eq',Finset.mem_range,show n-1<M by omega,if_true]
    have hlimit := (hDF V K hv).add (tendsto_const_nhds (x := Z))
    have hlimit' : Tendsto (fun M : ℕ => ∑ j ∈ Finset.range M,
        hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))*K (j+1))
        atTop (𝓝 ((fderiv ℂ F (SpectralWeight.one.toCoeff q)) V+Z)) := by
      apply hlimit.congr'
      filter_upwards [eventually_ge_atTop n] with M hM
      rw [Finset.sum_sub_distrib,hsum M hM]
      ring
    convert hlimit' using 1
    rw [hDA]
    congr 1
    change (fderiv ℂ ε _) V+(fderiv ℂ F _) V=(fderiv ℂ F _) V+Z
    rw [hDε]
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
