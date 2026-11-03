import NLS.KdV.HillDirichletGapTrigonometry
import NLS.ComplexAnalysis.CosineSegmentGeometry

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillDirichletGapCosine_im_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    (hillDirichletGapCosine q hq hr n hn).im = 0 := by
  rw [hillDirichletGapCosine,← ofReal_sub,← ofReal_div]
  exact ofReal_im _

theorem hillDirichletGapSine_im_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    (hillDirichletGapSine q hq hr n hn).im = 0 := by
  let μ := hillDirichletEnergy q hq hr n hn
  let S := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) μ
  have hS : S.im = 0 := by
    dsimp only [S,μ]
    rw [hillDirichletSheetRoot_at_dirichlet_eq_norming q hq hr n hn]
    exact ofReal_im _
  have hrot := im_I_mul_div_hillDeflatedEnergyCanonicalRoot_eq_zero_on_gap q hq hr n hn μ
    (hillDirichletEnergy_mem_gap q hq hr n hn) S hS
  have he : hillDirichletGapSine q hq hr n hn =
      (I*(S/hillDeflatedEnergyCanonicalRoot q hq hr n μ))/(hillRealGapHalfLength q hq hr n : ℂ) := by
    unfold hillDirichletGapSine
    dsimp only [μ,S]
    ring
  rw [he,div_ofReal_im,hrot,zero_div]

theorem exists_hillDirichlet_terminal_angle (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q hq hr n ≠ 0) :
    ∃ e : ℂ, e ∈ segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ∧
      cosineGapPoint (hillRealGapCenter q hq hr n) (hillRealGapHalfLength q hq hr n) e =
        (hillDirichletEnergy q hq hr n hn : ℂ) ∧
      Complex.cos e = hillDirichletGapCosine q hq hr n hn ∧
      Complex.sin e = hillDirichletGapSine q hq hr n hn := by
  let τ : ℂ := hillRealGapCenter q hq hr n
  let δ : ℂ := hillRealGapHalfLength q hq hr n
  let μ : ℂ := hillDirichletEnergy q hq hr n hn
  have hδ : δ ≠ 0 := ofReal_ne_zero.mpr hgap
  have hgeom := hillRealGapContour_geometry q hq hr n hn
  have hl : τ-δ = (hillRealLabels q hq hr (2*n-1) : ℂ) := by
    dsimp only [τ,δ]
    rw [← ofReal_sub,hgeom.2.2.1]
  have hu : τ+δ = (hillRealLabels q hq hr (2*n) : ℂ) := by
    dsimp only [τ,δ]
    rw [← ofReal_add,hgeom.2.2.2.1]
  have hμ : μ ∈ segment ℝ (τ-δ) (τ+δ) := by
    rw [hl,hu]
    exact ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n))
      (hillDirichletEnergy_mem_gap q hq hr n hn)
  obtain ⟨e,he,hpoint⟩ : ∃ e : ℂ, e ∈ segment ℝ (0 : ℂ) (Real.pi : ℂ) ∧ cosineGapPoint τ δ e = μ := by
    by_cases hleft : μ = τ-δ
    · exact ⟨Real.pi,right_mem_segment ℝ _ _,by simpa only [cosineGapPoint,Complex.cos_pi,mul_neg,mul_one,← sub_eq_add_neg] using hleft.symm⟩
    by_cases hright : μ = τ+δ
    · exact ⟨0,left_mem_segment ℝ _ _,by simpa only [cosineGapPoint,Complex.cos_zero,mul_one] using hright.symm⟩
    obtain ⟨e,he,_,hpoint⟩ := exists_cosineGapPoint_regular_angle τ δ μ hμ hleft hright
    exact ⟨e,he,hpoint⟩
  have hcos : Complex.cos e = hillDirichletGapCosine q hq hr n hn := by
    change Complex.cos e = (μ-τ)/δ
    apply (eq_div_iff hδ).mpr
    unfold cosineGapPoint at hpoint
    linear_combination hpoint
  have hsquare : Complex.sin e^2 = hillDirichletGapSine q hq hr n hn^2 := by
    have hs := hillDirichletGapSine_sq_add_cosine_sq q hq hr n hn hgap
    have ht := Complex.sin_sq_add_cos_sq e
    rw [hcos] at ht
    linear_combination ht-hs
  have him : e.im = 0 := im_eq_zero_of_mem_real_segment 0 Real.pi e he
  have hre : e.re ∈ Icc 0 Real.pi := re_mem_Icc_of_mem_real_segment 0 Real.pi Real.pi_pos.le e he
  have hreal : e = (e.re : ℂ) := by apply Complex.ext <;> simp [him]
  have heplus : e ∈ segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) := by
    rw [hreal,← ofReal_neg]
    exact ofReal_mem_ordered_segment _ _ _ (by linarith [Real.pi_pos]) ⟨by linarith [hre.1,Real.pi_pos],hre.2⟩
  have heminus : -e ∈ segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) := by
    rw [hreal,← ofReal_neg,← ofReal_neg]
    exact ofReal_mem_ordered_segment _ _ _ (by linarith [Real.pi_pos]) ⟨by linarith [hre.2],by linarith [hre.1,Real.pi_pos]⟩
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sin e) (hillDirichletGapSine q hq hr n hn) hsquare with hs | hs
  · exact ⟨e,heplus,hpoint,hcos,hs⟩
  · refine ⟨-e,heminus,?_,?_,?_⟩
    · simpa only [cosineGapPoint,Complex.cos_neg] using hpoint
    · simpa only [Complex.cos_neg] using hcos
    · rw [Complex.sin_neg,hs,neg_neg]

end NLS.KdV
