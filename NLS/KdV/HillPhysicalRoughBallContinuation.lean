import NLS.KdV.HillActionGapRatioRoughContinuation
import NLS.KdV.HillAbelianTerminalFactorAnalytic

/-! # Physical analytic germs continue across a whole rough ball -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

theorem hillPhysical_eq_on_rough_ball_of_scaling_germ
    (η : ℝ) (hη : 0 < η) (R : PeriodOneHminusOne → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (0 : PeriodOneHminusOne) η))
    (F : RealPeriodOneHillPotential → ℂ)
    (hF : ∀ p : RealPeriodOneHillPotential, ∀ t : ℝ,
      AnalyticAt ℝ (fun s => F (hillPhysicalRealScale p s)) t)
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (hgerm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      R (hillPhysicalHminusEmbedding p).val=F p)
    (p : RealPeriodOneHillPotential)
    (hp : (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η) :
    R (hillPhysicalHminusEmbedding p).val=F p := by
  let L : ℝ →L[ℝ] PeriodOneHminusOne :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (hillPhysicalHminusEmbedding p).val
  let U : Set ℝ := L ⁻¹' ball (0 : PeriodOneHminusOne) η
  let f : ℝ → ℂ := fun t => R (L t)
  let g : ℝ → ℂ := fun t => F (hillPhysicalRealScale p t)
  have hf : AnalyticOnNhd ℝ f U := fun t ht =>
    ((hR (L t) ht).restrictScalars (𝕜 := ℝ)).comp (L.analyticAt t)
  have hg : AnalyticOnNhd ℝ g U := fun t _ => hF p t
  have hU : IsPreconnected U :=
    ((convex_ball (0 : PeriodOneHminusOne) η).linear_preimage L.toLinearMap).isPreconnected
  have h0 : (0 : ℝ) ∈ U := by
    change L 0 ∈ ball 0 η
    rw [map_zero]
    exact mem_ball_self hη
  have h1 : (1 : ℝ) ∈ U := by
    simpa only [U,L,mem_preimage,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply,one_smul] using hp
  have hscale0 : hillPhysicalRealScale p 0=⟨0,h0q,h0r⟩ := by
    apply Subtype.ext
    simp only [hillPhysicalRealScale,ofReal_zero,zero_smul]
  have ht : Tendsto (hillPhysicalRealScale p) (𝓝 (0 : ℝ)) (𝓝 (hillPhysicalRealScale p 0)) :=
    (continuous_hillPhysicalRealScale p).tendsto 0
  rw [hscale0] at ht
  have he : f =ᶠ[𝓝 (0 : ℝ)] g := by
    filter_upwards [ht.eventually hgerm] with t ht0
    change R (L t)=_
    rw [hillPhysicalHminusEmbedding_realScale] at ht0
    exact ht0
  have hh := hf.eqOn_of_preconnected_of_eventuallyEq hg hU h0 he h1
  simpa only [f,g,L,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,
    one_smul,hillPhysicalRealScale,ofReal_one] using hh

theorem analyticAt_hillDirichletAbelianTerminalFactor_realScale
    (p : RealPeriodOneHillPotential) (n : ℕ+) (t : ℝ) :
    AnalyticAt ℝ (fun s => hillDirichletAbelianTerminalFactor (hillPhysicalRealScale p s).val
      (hillPhysicalRealScale p s).property.1 (hillPhysicalRealScale p s).property.2 (n : ℕ) n.property) t := by
  let q := hillPhysicalRealScale p t
  obtain ⟨T,hT,_hT0,_hDT,hmatch⟩ :=
    exists_hillDirichletAbelianTerminalFactor_analytic_extension q.val q.property.1 q.property.2
      (n : ℕ) n.property
  let P : ℝ → Coeff 2 := fun s => SpectralWeight.one.toCoeff (hillPhysicalRealScale p s).val
  have hP : AnalyticAt ℝ P t := by
    let L : ℝ →L[ℝ] Coeff 2 :=
      (ContinuousLinearMap.id ℝ ℝ).smulRight (SpectralWeight.one.toCoeff p.val)
    have he : P=L := by
      funext s
      simp only [P,hillPhysicalRealScale,map_smul]
      rfl
    rw [he]
    exact L.analyticAt t
  have ha := hT.restrictScalars (𝕜 := ℝ)
  have hlocal : AnalyticAt ℝ (fun s => T (P s)) t := ha.comp (f := P) hP
  have he := (continuous_hillPhysicalRealScale p).continuousAt.tendsto.eventually hmatch
  exact hlocal.congr he

theorem hillDirichletTerminal_normalized_eq_on_rough_ball_of_germ
    (η : ℝ) (hη : 0 < η) (n : ℕ+) (R : PeriodOneHminusOne → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (0 : PeriodOneHminusOne) η))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (hgerm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      R (hillPhysicalHminusEmbedding p).val=
        hillDirichletAbelianTerminalFactor p.val p.property.1 p.property.2 (n : ℕ) n.property/(n : ℂ))
    (p : RealPeriodOneHillPotential)
    (hp : (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η) :
    R (hillPhysicalHminusEmbedding p).val=
      hillDirichletAbelianTerminalFactor p.val p.property.1 p.property.2 (n : ℕ) n.property/(n : ℂ) := by
  exact hillPhysical_eq_on_rough_ball_of_scaling_germ η hη R hR
    (fun p => hillDirichletAbelianTerminalFactor p.val p.property.1 p.property.2 (n : ℕ) n.property/(n : ℂ))
    (fun p t => (analyticAt_hillDirichletAbelianTerminalFactor_realScale p n t).div_const)
    h0q h0r hgerm p hp

end NLS.KdV
