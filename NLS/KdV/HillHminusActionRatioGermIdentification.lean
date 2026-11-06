import NLS.ComplexAnalysis.AnalyticGermCancellation
import NLS.KdV.HillPhysicalGapGermNontrivial
import NLS.KdV.HillPhysicalRealGermIdentity
import NLS.KdV.HillHminusLocalActionAmplitude

/-! # Physical actions identify rough analytic ratios through closed gaps

Equality after multiplication by the squared half gap determines the
analytic ratio germ even though every gap is collapsed at zero. Actual
physical action matching therefore suffices for ratio matching on a whole
rough ball, without a smallness condition on the physical L2 norm.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillHminus_ratio_l2_germ_eq_of_gap_products
    (n : ℕ+) (R H : PeriodOneHminusOne → ℂ)
    (hR : AnalyticAt ℂ R 0) (hH : AnalyticAt ℂ H 0)
    (hprod : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      (hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)^2*
          R (hillPhysicalHminusEmbedding p).val =
        (hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)^2*
          H (hillPhysicalHminusEmbedding p).val) :
    (fun u => R (periodOneL2Inclusion u)) =ᶠ[𝓝 (0 : Coeff 2)]
      (fun u => H (periodOneL2Inclusion u)) := by
  let S : Coeff 2 → ℂ := fun u => hillHminusLocalGapSquare h0q h0r n (periodOneL2Inclusion u)
  obtain ⟨V,_hV,h0V,_hM,hS⟩ := exists_hillHminusLocalGapMoments_analytic h0q h0r n
  have hSa : AnalyticAt ℂ S 0 := by
    have ha : AnalyticAt ℂ (hillHminusLocalGapSquare h0q h0r n)
        (periodOneL2Inclusion (0 : Coeff 2)) := by simpa only [map_zero] using hS 0 h0V
    exact ha.comp (f := fun u : Coeff 2 => periodOneL2Inclusion u) (periodOneL2Inclusion.analyticAt 0)
  have hRa : AnalyticAt ℂ (fun u => R (periodOneL2Inclusion u)) 0 := by
    have ha : AnalyticAt ℂ R (periodOneL2Inclusion (0 : Coeff 2)) := by simpa only [map_zero] using hR
    exact ha.comp (f := fun u : Coeff 2 => periodOneL2Inclusion u) (periodOneL2Inclusion.analyticAt 0)
  have hHa : AnalyticAt ℂ (fun u => H (periodOneL2Inclusion u)) 0 := by
    have ha : AnalyticAt ℂ H (periodOneL2Inclusion (0 : Coeff 2)) := by simpa only [map_zero] using hH
    exact ha.comp (f := fun u : Coeff 2 => periodOneL2Inclusion u) (periodOneL2Inclusion.analyticAt 0)
  have hprodNative : (fun u => S u*R (periodOneL2Inclusion u)) =ᶠ[𝓝 (0 : Coeff 2)]
      (fun u => S u*H (periodOneL2Inclusion u)) := by
    apply eventuallyEq_native_of_physical_real_germ h0q h0r _ _ (hSa.mul hRa) (hSa.mul hHa)
    obtain ⟨W,hW,h0W,hmatch⟩ :=
      exists_hillLocalGapSymmetricData_physical_neighborhood 0 h0q h0r (n : ℕ) n.property
    filter_upwards [hprod,hW.mem_nhds h0W] with p hp hpW
    have hgap : S (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))=
        (2*(hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ))^2 := by
      change hillHminusLocalGapSquare h0q h0r n
        (periodOneL2Inclusion (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)))=_
      rw [hillHminusLocalGapSquare_l2,hillPeriodDouble_unitSample _ p.property.1]
      exact (hmatch p hpW).2
    simp only [Pi.mul_apply]
    rw [hgap]
    change (2*(hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ))^2*
        R (hillPhysicalHminusEmbedding p).val =
      (2*(hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ))^2*
        H (hillPhysicalHminusEmbedding p).val
    calc
      _ = 4*((hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)^2*
          R (hillPhysicalHminusEmbedding p).val) := by ring
      _ = 4*((hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)^2*
          H (hillPhysicalHminusEmbedding p).val) := by rw [hp]
      _ = _ := by ring
  exact analytic_germ_cancel_eq hSa hRa hHa hprodNative
    (hillHminusLocalGapSquare_l2_germ_nontrivial h0q h0r n)

theorem hillHminus_ratio_physical_germ_eq_of_gap_products
    (n : ℕ+) (R H : PeriodOneHminusOne → ℂ)
    (hR : AnalyticAt ℂ R 0) (hH : AnalyticAt ℂ H 0)
    (hprod : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      (hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)^2*
          R (hillPhysicalHminusEmbedding p).val =
        (hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)^2*
          H (hillPhysicalHminusEmbedding p).val) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      R (hillPhysicalHminusEmbedding p).val = H (hillPhysicalHminusEmbedding p).val := by
  have ht : Tendsto (fun p : RealPeriodOneHillPotential =>
      Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))
      (𝓝 ⟨0,h0q,h0r⟩) (𝓝 (0 : Coeff 2)) := by
    simpa only [Function.comp_def,map_zero] using
      ((Fourier.paritySample (p := 2) 0).continuous.comp
        (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val)).tendsto
          (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
  exact ht.eventually (hillHminus_ratio_l2_germ_eq_of_gap_products h0q h0r n R H hR hH hprod)

theorem hillHminus_action_ratio_germ_of_physical_actions
    (n : ℕ+) (R : PeriodOneHminusOne → ℂ) (hR : AnalyticAt ℂ R 0)
    (haction : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      (hillRealGapIntegral p.val p.property.1 p.property.2 (n : ℕ) 0 : ℂ)=
        (hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)^2*
          R (hillPhysicalHminusEmbedding p).val) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      R (hillPhysicalHminusEmbedding p).val =
        hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) := by
  have hlocal := hillHminusLocalActionGapRatio_eventually_eq_physical h0q h0r n
  have he := hillHminus_ratio_physical_germ_eq_of_gap_products h0q h0r n R
    (hillHminusLocalActionGapRatio h0q h0r n) hR
    (analyticAt_hillHminusLocalActionGapRatio_zero h0q h0r n) (by
      filter_upwards [haction,hlocal] with p hp hpL
      rw [hpL,← hillRealGapIntegral_eq_halfLength_sq_mul_ratio p.val p.property.1 p.property.2
        (n : ℕ) n.property]
      exact hp.symm)
  filter_upwards [he,hlocal] with p hp hpL
  exact hp.trans hpL

theorem hillHminus_action_ratio_eq_on_ball_of_physical_action_germ
    (η : ℝ) (hη : 0 < η) (n : ℕ+) (R : PeriodOneHminusOne → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (0 : PeriodOneHminusOne) η))
    (haction : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      (hillRealGapIntegral p.val p.property.1 p.property.2 (n : ℕ) 0 : ℂ)=
        (hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)^2*
          R (hillPhysicalHminusEmbedding p).val)
    (p : RealPeriodOneHillPotential)
    (hp : (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η) :
    R (hillPhysicalHminusEmbedding p).val =
      hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) := by
  exact hillActionGapRatio_eq_on_rough_ball_of_germ η hη (n : ℕ) n.property R hR h0q h0r
    (hillHminus_action_ratio_germ_of_physical_actions h0q h0r n R (hR 0 (mem_ball_self hη))
      haction) p hp

end NLS.KdV
