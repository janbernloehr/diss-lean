import NLS.KdV.HillFreePhysicalRootAmplitude
import NLS.KdV.HillPhysicalCubicFactor

/-! # The actual cubic Hill moment's analytic fourth-gap coefficient at zero -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- A rough-source analytic coefficient gives the literal physical cubic
moment its fourth half-gap factor, including when the gap is collapsed.
The free coefficient is computed from the actual normalized amplitude. -/
theorem exists_hillFree_analytic_cubic_gap_factor (n : ℕ+) :
    ∃ C : PeriodOneHminusOne → ℂ, AnalyticAt ℂ C 0 ∧
      C 0=-3/(32*(n : ℂ)^3*(Real.pi : ℂ)^3) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
        hillHminusRealGapCubicContourMoment (hillOriginalHminusSource p.val)
          (hillOriginalHminusSource_real p.val p.property.2) n =
          (hillHminusLocalGapSquare h0q h0r n (hillOriginalHminusSource p.val)/4)^2*
            C (hillOriginalHminusSource p.val) := by
  obtain ⟨ρ,hρ,V,hV,h0V,Q,hQ,hQ0,hphys⟩ := exists_hillFree_physical_root_amplitude h0q h0r n
  let s : PeriodOneHminusOne → ℂ := fun q => hillHminusLocalGapSquare h0q h0r n q/4
  let C : PeriodOneHminusOne → ℂ := cubicRootAmplitudeFactor Q s
  obtain ⟨U,_hU,h0U,_hM,hS⟩ := exists_hillHminusLocalGapMoments_analytic h0q h0r n
  have hs : AnalyticAt ℂ s 0 := (hS 0 h0U).div_const
  have hs0 : s 0=0 := by
    dsimp only [s]
    rw [(hillHminusLocalGapMoments_zero h0q h0r n).2,zero_div]
  have hC : AnalyticAt ℂ C 0 := analyticAt_cubicRootAmplitudeFactor Q s 0 ρ hρ V hV h0V hQ hs hs0
  have hC0 : C 0=-3/(32*(n : ℂ)^3*(Real.pi : ℂ)^3) := by
    change cubicRootAmplitudeFactor Q s 0=_
    rw [cubicRootAmplitudeFactor_at_collapse Q s 0 hs0,hQ0]
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.pos.ne'
    have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hn,hp]
    norm_num [pow_succ]
  refine ⟨C,hC,hC0,?_⟩
  filter_upwards [hphys,hillHminusLocalGapData_eventually_eq_original h0q h0r n] with p hp hpdata
  obtain ⟨hpV,R,hdR,hRρ,hRcan,hamp⟩ := hp
  let τ : ℂ := hillRealGapCenter p.val p.property.1 p.property.2 (n : ℕ)
  let δ : ℝ := hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ)
  have hQshift : AnalyticOnNhd ℂ (fun z => Q (z-τ,hillOriginalHminusSource p.val)) (closedBall τ R) := by
    intro z hz
    have hw : z-τ ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball,dist_zero_right]
      exact (show ‖z-τ‖ ≤ R by simpa only [mem_closedBall,dist_eq_norm] using hz).trans_lt hRρ
    exact (hQ _ ⟨hw,hpV⟩).comp
      (f := fun z : ℂ => (z-τ,hillOriginalHminusSource p.val))
      ((analyticAt_id.sub analyticAt_const).prod analyticAt_const)
  have hi := hillL2RealCubicContourMoment_eq_root_factor p.val p.property.1 p.property.2 (n : ℕ) n.property
    Q s (hillOriginalHminusSource p.val) hpdata.2.symm R hdR hRcan hQshift hamp
  have he := (hillHminusRealGapCubicContourMoment_original_source p n).trans hi
  apply he.trans
  change (δ : ℂ)^4*C (hillOriginalHminusSource p.val)=s (hillOriginalHminusSource p.val)^2*C (hillOriginalHminusSource p.val)
  change (δ : ℂ)^4*_=(hillHminusLocalGapSquare h0q h0r n (hillOriginalHminusSource p.val)/4)^2*_
  rw [hpdata.2]
  ring

end NLS.KdV
