import NLS.KdV.HillHminusHighRootPhysicalSquares
import NLS.KdV.HillAbelianCoordinateFactor
import NLS.KdV.HillDirichletLabelContinuity

/-! # The normalized rough high root is the original physical root germ -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillHminus_high_root_center_physical_germ
    (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (r : ℝ) (hr : 0 < r)
    (V : Set PeriodOneHminusOne) (hV : IsOpen V) (h0V : (0 : PeriodOneHminusOne) ∈ V)
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u)
    (U : ℂ × PeriodOneHminusOne → ℂ)
    (hUa : AnalyticOnNhd ℂ U
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V))
    (hU0 : U ((((Real.pi : ℂ)*(n : ℕ))^2),0)=
      (n : ℂ)*hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) (((Real.pi : ℂ)*(n : ℕ))^2))
    (hfac : ∀ t ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V,
      hillHminusRadicand t.2 t.1=hillHminusGapPolynomial n r t*(U t/(n : ℂ))^2) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      U ((((Real.pi : ℂ)*(n : ℕ))^2),hillOriginalHminusSource p.val)/(n : ℂ)=
        hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ) (((Real.pi : ℂ)*(n : ℕ))^2) := by
  let c : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  let p0 : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  let F : RealPeriodOneHillPotential → ℂ := fun p => U (c,hillOriginalHminusSource p.val)/(n : ℂ)
  let G : RealPeriodOneHillPotential → ℂ := fun p =>
    hillLocalDeflatedComplexRoot 0 h0q h0r (n : ℕ) (c,SpectralWeight.one.toCoeff p.val)
  have hR : 0 < Real.pi*(n : ℕ)*r := by positivity
  have hc : (hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ)=c := by
    rw [hillFreeGapCenter h0q h0r (n : ℕ) n.property]
    simp only [freeHillValue,Int.cast_natCast,ofReal_mul,ofReal_pow,ofReal_natCast]
    dsimp only [c]
    ring
  have hR0 : 0 < hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ) :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).1
      (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).2.1
  have hcb : c ∈ ball (hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ)
      (hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ)) := by
    rw [hc]
    exact mem_ball_self hR0
  have hdom0 := mem_hillLocalDeflatedRootDomain_base 0 h0q h0r (n : ℕ) n.property c hcb
  have hF : ContinuousAt F p0 := by
    have ha : ContinuousAt U (c,hillOriginalHminusSource p0.val) := by
      simpa only [p0,map_zero] using (hUa (c,0) ⟨mem_ball_self hR,h0V⟩).continuousAt
    exact (ha.comp (f := fun p : RealPeriodOneHillPotential => (c,hillOriginalHminusSource p.val))
      (continuous_const.prodMk
        (hillOriginalHminusSource.continuous.comp continuous_subtype_val)).continuousAt).div_const _
  have hG : ContinuousAt G p0 := by
    have ha : ContinuousAt (hillLocalDeflatedComplexRoot 0 h0q h0r (n : ℕ))
        (c,SpectralWeight.one.toCoeff p0.val) := by
      simpa only [p0,map_zero] using
        (analyticOnNhd_hillLocalDeflatedComplexRoot 0 h0q h0r (n : ℕ) n.property _ hdom0).continuousAt
    exact ha.comp (f := fun p : RealPeriodOneHillPotential => (c,SpectralWeight.one.toCoeff p.val))
      (continuous_const.prodMk (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val)).continuousAt
  have hF0 : F p0=hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) c := by
    have hu : U (c,0)=(n : ℂ)*hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) c := hU0
    have hnn : (n : ℂ)≠0 := by exact_mod_cast n.ne_zero
    calc
      F p0=U (c,0)/(n : ℂ) := by simp only [F,p0,map_zero]
      _ = ((n : ℂ)*hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) c)/(n : ℂ) :=
        congrArg (fun z : ℂ => z/(n : ℂ)) hu
      _ = _ := mul_div_cancel_left₀ _ hnn
  have hG0 : G p0=hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) c :=
    hillLocalDeflatedComplexRoot_base 0 h0q h0r (n : ℕ) n.property c hcb
  have hGn : G p0≠0 := hillLocalDeflatedComplexRoot_ne_zero 0 h0q h0r
    (n : ℕ) n.property _ hdom0
  obtain ⟨s,W,hs,hW,h0W,hdata⟩ := exists_hillHminus_high_root_physical_square_neighborhood
    h0q h0r n hn r hr V hV h0V hpairs U hUa hfac
  have hsq : ∀ᶠ p in 𝓝 p0, (F p)^2=(G p)^2 := by
    filter_upwards [hW.mem_nhds h0W] with p hp
    have hh := hdata p hp c (mem_ball_self hs)
    exact hh.2.2.2.trans (congrArg (fun z : ℂ => z^2) hh.2.2.1.symm)
  have he := eventuallyEq_of_sq_eq_of_continuousAt F G p0 hF hG (hF0.trans hG0.symm) hGn hsq
  filter_upwards [he,hW.mem_nhds h0W] with p hp hpW
  exact hp.trans (hdata p hpW c (mem_ball_self hs)).2.2.1

theorem hillHminus_high_root_dirichlet_physical_germ
    (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (r : ℝ) (hr : 0 < r)
    (V : Set PeriodOneHminusOne) (hV : IsOpen V) (h0V : (0 : PeriodOneHminusOne) ∈ V)
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u)
    (U : ℂ × PeriodOneHminusOne → ℂ)
    (hUa : AnalyticOnNhd ℂ U
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V))
    (hU0 : U ((((Real.pi : ℂ)*(n : ℕ))^2),0)=
      (n : ℂ)*hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) (((Real.pi : ℂ)*(n : ℕ))^2))
    (hfac : ∀ t ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V,
      hillHminusRadicand t.2 t.1=hillHminusGapPolynomial n r t*(U t/(n : ℂ))^2) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      U ((hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property : ℂ),
        (hillPhysicalHminusEmbedding p).val)/(n : ℂ)=
          hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ)
            (hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property) := by
  let c : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  let p0 : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  let μ : RealPeriodOneHillPotential → ℂ := fun p => hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property
  have hμ : Continuous μ := continuous_ofReal.comp (continuous_hillDirichletEnergy (n : ℕ) n.property)
  have hc : (hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ)=c := by
    rw [hillFreeGapCenter h0q h0r (n : ℕ) n.property]
    simp only [freeHillValue,Int.cast_natCast,ofReal_mul,ofReal_pow,ofReal_natCast]
    dsimp only [c]
    ring
  have hμ0 : μ p0=c := by
    change (hillDirichletEnergy 0 h0q h0r (n : ℕ) n.property : ℂ)=c
    rw [hillDirichletEnergy_eq_center_of_halfLength_zero 0 h0q h0r (n : ℕ) n.property
      (hillFreeGapHalfLength h0q h0r (n : ℕ) n.property)]
    exact hc
  obtain ⟨s,W,hs,hW,h0W,hdata⟩ := exists_hillHminus_high_root_physical_square_neighborhood
    h0q h0r n hn r hr V hV h0V hpairs U hUa hfac
  have ht : Tendsto μ (𝓝 p0) (𝓝 c) := by simpa only [hμ0] using hμ.tendsto p0
  filter_upwards [hillHminus_high_root_center_physical_germ h0q h0r n hn r hr V hV h0V hpairs U hUa hU0 hfac,
    hW.mem_nhds h0W,ht.eventually (ball_mem_nhds c hs)] with p hp0 hpW hpμ
  have hleft : ContinuousOn (fun z => U (z,hillOriginalHminusSource p.val)/(n : ℂ)) (ball c s) := by
    intro z hz
    exact (((hUa (z,hillOriginalHminusSource p.val) (hdata p hpW z hz).1).comp
      (f := fun z : ℂ => (z,hillOriginalHminusSource p.val))
      (analyticAt_id.prod analyticAt_const)).div_const).continuousAt.continuousWithinAt
  have hright : ContinuousOn (hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ)) (ball c s) :=
    (analyticOnNhd_hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ)).continuousOn.mono
      (fun z hz => (hdata p hpW z hz).2.1)
  have he := (convex_ball c s).isPreconnected.eq_of_sq_eq hleft hright
    (fun z hz => (hdata p hpW z hz).2.2.2)
    (fun {z} hz => hillDeflatedEnergyCanonicalRoot_ne_zero p.val p.property.1 p.property.2 (n : ℕ)
      n.property z (hdata p hpW z hz).2.1) (mem_ball_self hs) hp0
  exact he hpμ

end NLS.KdV
