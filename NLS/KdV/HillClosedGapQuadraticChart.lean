import NLS.KdV.HillDeflatedCosineMean
import NLS.ComplexAnalysis.AnalyticCollapsedQuadraticSolution

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem exists_hillRegularAbelian_closed_gap_quadratic_chart
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hc : hillRealLabels q hq hr (2*k-1) = hillRealLabels q hq hr (2*k)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ U : Set (Coeff 2), IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧
      ∃ Q : ℂ × Coeff 2 → ℂ, AnalyticOnNhd ℂ Q (ball (0:ℂ) ρ ×ˢ U) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        SpectralWeight.one.toCoeff p.val ∈ U ∧ ‖(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ)‖ < ρ ∧
        ∀ w ∈ ball (0:ℂ) ρ,
          (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ)+w ∈ hillGapFilledDomain p.val p.property.1 p.property.2 k ∧
          (w^2-(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ)^2)*
              deriv (fun z => Q (z,SpectralWeight.one.toCoeff p.val)) w+w*Q (w,SpectralWeight.one.toCoeff p.val) =
            -I*hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn
                ((hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ)+w)/
              hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k
                ((hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ)+w)-(if k=n then 1 else 0) := by
  obtain ⟨H,E,V,W,hE,hV,hW,hgapE,hqV,hqW,hH,hm,hphysical⟩ :=
    exists_hillDeflatedDifferential_analytic_mean_chart q hq hr h0q h0r n k hn hk
  obtain ⟨A,_,hqA,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  have hbaseData := hillLocalGapSymmetricData_eq_physical_of_geometry q hq hr q hq hr k hk
    (hillRealGapContour_band_bounds q hq hr k hk)
    (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk)
  let τ := hillLocalGapMidpoint q hq hr k
  let s : Coeff 2 → ℂ := fun p => hillLocalGapSquare q hq hr k p/4
  let f : ℂ × Coeff 2 → ℂ := fun t => H (τ t.2+t.1,t.2)
  have hhalf0 : hillRealGapHalfLength q hq hr k = 0 := by simp [hillRealGapHalfLength,hc]
  have hs0 : s (SpectralWeight.one.toCoeff q) = 0 := by
    dsimp only [s]
    rw [hbaseData.2,hhalf0,ofReal_zero,mul_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_div]
  have hτ : AnalyticAt ℂ τ (SpectralWeight.one.toCoeff q) := hM _ hqA
  have hs : AnalyticAt ℂ s (SpectralWeight.one.toCoeff q) := (hS _ hqA).div_const
  have hcenter : hillRealGapCenter q hq hr k = hillRealLabels q hq hr (2*k-1) := by
    dsimp only [hillRealGapCenter]
    rw [← hc]
    ring
  have hpoint : τ (SpectralWeight.one.toCoeff q) ∈ E := by
    dsimp only [τ]
    rw [hbaseData.1,hcenter]
    exact hgapE (left_mem_segment ℝ _ _)
  let T : ℂ × Coeff 2 → ℂ × Coeff 2 := fun t => (τ t.2+t.1,t.2)
  have hτJ : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => τ t.2) ((0:ℂ),SpectralWeight.one.toCoeff q) :=
    AnalyticAt.comp (𝕜 := ℂ) (x := ((0:ℂ),SpectralWeight.one.toCoeff q)) (g := τ)
      (f := fun t : ℂ × Coeff 2 => t.2) hτ analyticAt_snd
  have hT : AnalyticAt ℂ T ((0:ℂ),SpectralWeight.one.toCoeff q) :=
    (hτJ.add analyticAt_fst).prod analyticAt_snd
  have hTpoint : T ((0:ℂ),SpectralWeight.one.toCoeff q) ∈ E ×ˢ V := by
    exact ⟨by simpa only [T,add_zero] using hpoint,hqV⟩
  have hf : AnalyticAt ℂ f ((0:ℂ),SpectralWeight.one.toCoeff q) :=
    (hH _ hTpoint).comp (f := T) hT
  obtain ⟨R,hR,U,hU,hqU,Q,hQ,hsol⟩ := exists_analytic_centered_mean_free_quadratic_solution f s
    (SpectralWeight.one.toCoeff q) hf hs hs0
  have hnear : T ⁻¹' (E ×ˢ V) ∈ 𝓝 ((0:ℂ),SpectralWeight.one.toCoeff q) :=
    hT.continuousAt.preimage_mem_nhds ((hE.prod hV).mem_nhds hTpoint)
  obtain ⟨B,hBsub,hB,hbaseB⟩ := _root_.mem_nhds_iff.mp hnear
  obtain ⟨C,O,hC,hO,h0C,hqO,hCO⟩ := isOpen_prod_iff.mp hB 0 (SpectralWeight.one.toCoeff q) hbaseB
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hC.mem_nhds h0C)
  let ρ := min (R/2) (ε/2)
  have hρ : 0 < ρ := lt_min (half_pos hR) (half_pos hε)
  have hρR : ρ < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hρε : ρ < ε := (min_le_right _ _).trans_lt (half_lt_self hε)
  let S := {p | AnalyticAt ℂ s p} ∩ {p | ‖s p‖ < ρ^2}
  have hSopen : IsOpen S :=
    (show ContinuousOn (fun p => ‖s p‖) {p | AnalyticAt ℂ s p} from
      fun p hp => hp.continuousAt.norm.continuousWithinAt).isOpen_inter_preimage (isOpen_analyticAt ℂ s) isOpen_Iio
  let Z := (U ∩ O) ∩ S
  have hZ : IsOpen Z := (hU.inter hO).inter hSopen
  have hqZ : SpectralWeight.one.toCoeff q ∈ Z := ⟨⟨hqU,hqO⟩,hs,by change ‖s (SpectralWeight.one.toCoeff q)‖ < ρ^2;rw [hs0,norm_zero];exact sq_pos_of_pos hρ⟩
  have hmean (p : Coeff 2) : parametricCosineMean f (fun _ => 0) (sqrt (s p),p) = hillLocalGapCosineMean q hq hr H k p := by
    simp only [parametricCosineMean,f,τ,s,hillLocalGapCosineMean,zero_add]
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  obtain ⟨Y,hY,hqY,hdata⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr k hk
  refine ⟨ρ,hρ,Z,hZ,hqZ,Q,hQ.mono (prod_mono (ball_subset_ball hρR.le) (fun _ hp => hp.1.1)),?_⟩
  filter_upwards [hW.mem_nhds hqW,hY.mem_nhds hqY,hP.continuousAt.tendsto.eventually (hZ.mem_nhds hqZ)] with p hpW hpY hpZ
  have hsp : s (P p) = (hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ)^2 := by
    dsimp only [s,P]
    rw [(hdata p hpY).2]
    ring
  have hhalf : ‖(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ)‖ < ρ := by
    have hn : ‖(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ)‖^2 < ρ^2 := by
      rw [← norm_pow,← hsp]
      exact hpZ.2.2
    nlinarith [norm_nonneg (hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ)]
  refine ⟨hpZ,hhalf,?_⟩
  intro w hw
  have hmemb : (w,P p) ∈ B := hCO ⟨hball (ball_subset_ball hρε.le hw),hpZ.1.2⟩
  have henergy : (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ)+w ∈ E := by
    have hh := (hBsub hmemb).1
    change τ (P p)+w ∈ E at hh
    dsimp only [τ,P] at hh
    rwa [(hdata p hpY).1] at hh
  refine ⟨((hphysical p hpW).2.2 _ henergy).1,?_⟩
  have heq := (hsol (P p) hpZ.1.1).2 w (ball_subset_ball hρR.le hw)
  rw [quadraticRootPolynomial,sub_zero,hsp] at heq
  rw [heq,centeredMeanFree,hmean,(hphysical p hpW).2.1]
  have hconst : ((Real.pi : ℂ)*(if k=n then 1 else 0))/(Real.pi : ℂ) = (if k=n then 1 else 0) := by
    field_simp
  rw [hconst]
  change H (τ (P p)+w,P p)-_ = _
  dsimp only [τ,P]
  rw [(hdata p hpY).1,((hphysical p hpW).2.2 _ henergy).2]

end NLS.KdV
