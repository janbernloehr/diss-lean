import NLS.KdV.HillFreeQuadraticPrimitive
import NLS.KdV.HillPhysicalGapPrimitive
import NLS.KdV.HillHminusOriginalSourceAdapter

/-! # Physical matching of the centered rough trace data near the free source -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillHminusLocalDeflatedTrace_original_source (n : ℕ+) (p : RealPeriodOneHillPotential) (z : ℂ) :
    hillHminusLocalDeflatedTrace h0q h0r n (z,hillOriginalHminusSource p.val)=
      hillLocalDeflatedTraceNumerator 0 h0q h0r (n : ℕ) (z,SpectralWeight.one.toCoeff p.val) := by
  have h := hillHminusLocalDeflatedTrace_l2 h0q h0r n
    (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)) z
  rw [hillPeriodDouble_unitSample _ p.property.1] at h
  exact h

theorem hillHminusLocalGapData_eventually_eq_original (n : ℕ+) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      hillHminusLocalGapMidpoint h0q h0r n (hillOriginalHminusSource p.val)=
        (hillRealGapCenter p.val p.property.1 p.property.2 (n : ℕ) : ℂ) ∧
      hillHminusLocalGapSquare h0q h0r n (hillOriginalHminusSource p.val)/4=
        (hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)^2 := by
  obtain ⟨V,hV,h0V,hdata⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood 0 h0q h0r (n : ℕ) n.property
  filter_upwards [hV.mem_nhds h0V] with p hp
  have hτ := hillHminusLocalGapMidpoint_l2 h0q h0r n
    (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))
  have hs := hillHminusLocalGapSquare_l2 h0q h0r n
    (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))
  rw [hillPeriodDouble_unitSample _ p.property.1] at hτ hs
  refine ⟨hτ.trans (hdata p hp).1,?_⟩
  change hillHminusLocalGapSquare h0q h0r n
    (periodOneL2Inclusion (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)))/4=_
  rw [hs,(hdata p hp).2]
  ring

/-- The actual rough trace matches the original physical numerator on a
single fixed spectral disc, uniformly before the spectral variable. -/
theorem exists_hillCenteredFreeTrace_physical_disc (n : ℕ+) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      ∀ w ∈ ball (0 : ℂ) ε,
        hillCenteredFreeTrace h0q h0r n (w,hillOriginalHminusSource p.val)=
          hillDeflatedTraceNumerator p.val p.property.1 p.property.2 (n : ℕ)
            ((hillRealGapCenter p.val p.property.1 p.property.2 (n : ℕ) : ℂ)+w) := by
  obtain ⟨E,V,hE,hV,hgap,h0V,hmatch⟩ :=
    exists_hillLocalDeflatedTraceNumerator_physical_neighborhood 0 h0q h0r (n : ℕ) n.property
  let c : ℂ := hillRealGapCenter 0 h0q h0r (n : ℕ)
  have hcE : c ∈ E := by
    have hc : c=(hillRealLabels 0 h0q h0r (2*(n : ℕ)-1) : ℂ) :=
      congrArg Complex.ofReal ((hillFreeGapCenter h0q h0r (n : ℕ) n.property).trans
        (hillFreeGapEndpoints h0q h0r (n : ℕ) n.property).1.symm)
    rw [hc]
    exact hgap (left_mem_segment ℝ _ _)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hE.mem_nhds hcE)
  let τ : RealPeriodOneHillPotential → ℂ := fun p => hillRealGapCenter p.val p.property.1 p.property.2 (n : ℕ)
  have hτ : Continuous τ := continuous_ofReal.comp (continuous_hillRealGapCenter (n : ℕ))
  have hnear : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩, τ p ∈ ball c (r/2) :=
    hτ.continuousAt.preimage_mem_nhds (ball_mem_nhds c (half_pos hr))
  refine ⟨r/2,half_pos hr,?_⟩
  filter_upwards [hV.mem_nhds h0V,hnear,hillHminusLocalGapData_eventually_eq_original h0q h0r n] with p hpV hpτ hpdata
  intro w hw
  have hz : τ p+w ∈ E := hball (by
    rw [mem_ball,dist_eq_norm]
    have h1 : ‖τ p-c‖ < r/2 := by simpa only [mem_ball,dist_eq_norm] using hpτ
    have h2 : ‖w‖ < r/2 := by simpa only [mem_ball,dist_zero_right] using hw
    calc
      ‖τ p+w-c‖ = ‖(τ p-c)+w‖ := by congr 1;ring
      _ ≤ ‖τ p-c‖+‖w‖ := norm_add_le _ _
      _ < r := by linarith)
  rw [hillCenteredFreeTrace,hpdata.1,hillHminusLocalDeflatedTrace_original_source]
  exact (hmatch p hpV (τ p+w) hz).2.2

theorem hillCenteredFreeTrace_cosine_mean_eventually_zero (n : ℕ+) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      parametricCosineMean (hillCenteredFreeTrace h0q h0r n) (fun _ => 0)
        (sqrt (hillHminusLocalGapSquare h0q h0r n (hillOriginalHminusSource p.val)/4),
          hillOriginalHminusSource p.val)=0 := by
  obtain ⟨ε,hε,htrace⟩ := exists_hillCenteredFreeTrace_physical_disc h0q h0r n
  let δ : RealPeriodOneHillPotential → ℂ := fun p => hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ)
  have hδ : Continuous δ := continuous_ofReal.comp (continuous_hillRealGapHalfLength (n : ℕ))
  have hδ0 : δ ⟨0,h0q,h0r⟩=0 := by
    simpa only [δ,ofReal_zero] using! congrArg Complex.ofReal
      (hillFreeGapHalfLength h0q h0r (n : ℕ) n.property)
  have hnear : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩, ‖δ p‖ < ε := by
    have hh := hδ.continuousAt.preimage_mem_nhds (ball_mem_nhds (δ ⟨0,h0q,h0r⟩) hε)
    rw [hδ0] at hh
    filter_upwards [hh] with p hp
    change δ p ∈ ball (0 : ℂ) ε at hp
    simpa only [mem_ball,dist_zero_right] using hp
  filter_upwards [htrace,hnear,hillHminusLocalGapData_eventually_eq_original h0q h0r n] with p hp hpδ hpdata
  have hs : sqrt (hillHminusLocalGapSquare h0q h0r n (hillOriginalHminusSource p.val)/4)^2=(δ p)^2 :=
    (complex_sqrt_sq _).trans hpdata.2
  have hm : parametricCosineMean (hillCenteredFreeTrace h0q h0r n) (fun _ => 0)
      (sqrt (hillHminusLocalGapSquare h0q h0r n (hillOriginalHminusSource p.val)/4),hillOriginalHminusSource p.val)=
      parametricCosineMean (hillCenteredFreeTrace h0q h0r n) (fun _ => 0) (δ p,hillOriginalHminusSource p.val) := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with he | he
    · rw [he]
    · rw [he,parametricCosineMean_neg]
  rw [hm,parametricCosineMean]
  have hi := integral_hillDeflatedTraceNumerator_cosine_eq_zero p.val p.property.1 p.property.2 (n : ℕ) n.property
  apply Eq.trans ?_ hi
  apply intervalIntegral.integral_congr
  intro θ _hθ
  have hw : δ p*(Real.cos θ : ℂ) ∈ ball (0 : ℂ) ε := by
    rw [mem_ball,dist_zero_right,norm_mul]
    have hc : ‖(Real.cos θ : ℂ)‖ ≤ 1 := by simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    exact (mul_le_mul_of_nonneg_left hc (norm_nonneg (δ p))).trans_lt (by simpa only [mul_one] using hpδ)
  simpa only [zero_add,cosineGapPoint,←ofReal_cos,δ] using hp _ hw

end NLS.KdV
