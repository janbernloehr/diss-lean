import NLS.KdV.HillDeflatedDifferentialAnalyticCharts
import NLS.KdV.HillOpenGapHalfLength
import NLS.KdV.HillAbelianCosinePrimitive
import NLS.ComplexAnalysis.ParametricCosineRealAngleChart

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

theorem exists_hillAbelianCosinePrimitive_joint_analytic_open_gap_chart
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hgap : hillRealGapHalfLength q hq hr k ≠ 0) :
    ∃ F : ℂ × Coeff 2 → ℂ, ∃ Ω : Set ℂ, ∃ Z : Set (Coeff 2), ∃ W : Set RealPeriodOneHillPotential,
      IsOpen Ω ∧ Convex ℝ Ω ∧ segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ⊆ Ω ∧
      IsOpen Z ∧ SpectralWeight.one.toCoeff q ∈ Z ∧ IsOpen W ∧
      (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ W ∧ AnalyticOnNhd ℂ F (Ω ×ˢ Z) ∧
      (∀ p : Coeff 2, F ((Real.pi : ℂ),p) = 0) ∧
      ∀ p ∈ W, SpectralWeight.one.toCoeff p.val ∈ Z ∧ ∀ θ ∈ Ω,
        F (θ,SpectralWeight.one.toCoeff p.val) = hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k θ := by
  obtain ⟨H,E,U,V,hE,hU,hV,hgapE,hqU,hqV,hH,hHphysical⟩ :=
    exists_hillDeflatedNormalizedDifferential_analytic_gap_chart q hq hr h0q h0r n k hn hk
  obtain ⟨A,_,hqA,hM,_,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  have hM0 := (hillLocalGapSymmetricData_eq_physical_of_geometry q hq hr q hq hr k hk
    (hillRealGapContour_band_bounds q hq hr k hk)
    (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk)).1
  obtain ⟨d,hd,hd0,_,hdphysical⟩ := exists_hillGapHalfLength_analytic_extension q hq hr k hk hgap
  let τ := hillLocalGapMidpoint q hq hr k
  let O : Set (Coeff 2) := U ∩ ({p | AnalyticAt ℂ τ p} ∩ {p | AnalyticAt ℂ d p})
  have hO : IsOpen O := hU.inter ((isOpen_analyticAt ℂ τ).inter (isOpen_analyticAt ℂ d))
  have hqO : SpectralWeight.one.toCoeff q ∈ O := ⟨hqU,hM _ hqA,hd⟩
  have hτ : AnalyticOnNhd ℂ τ O := fun _ hp => hp.2.1
  have hδ : AnalyticOnNhd ℂ d O := fun _ hp => hp.2.2
  have hgeom := hillRealGapContour_geometry q hq hr k hk
  have hl : τ (SpectralWeight.one.toCoeff q)-d (SpectralWeight.one.toCoeff q) =
      (hillRealLabels q hq hr (2*k-1) : ℂ) := by
    dsimp only [τ]
    rw [hM0,hd0,← ofReal_sub,hgeom.2.2.1]
  have hu : τ (SpectralWeight.one.toCoeff q)+d (SpectralWeight.one.toCoeff q) =
      (hillRealLabels q hq hr (2*k) : ℂ) := by
    dsimp only [τ]
    rw [hM0,hd0,← ofReal_add,hgeom.2.2.2.1]
  obtain ⟨Z,Ω,hZ,hqZ,hZO,hΩ,hconv,hangle,hchart⟩ := exists_local_parametricCosine_chart_on_real_segment
    τ d O hO hτ hδ (E ×ˢ U) (hE.prod hU) (SpectralWeight.one.toCoeff q) hqO (-Real.pi) Real.pi
    (by intro z hz; rw [hl,hu] at hz; exact ⟨hgapE hz,hqU⟩)
  have hangle' : segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ⊆ Ω := by simpa only [ofReal_neg] using hangle
  have hπ : (Real.pi : ℂ) ∈ Ω := hangle' (right_mem_segment ℝ _ _)
  have hspec := parametricCosinePrimitive_spec H τ d (E ×ˢ U) Ω Z hΩ hconv hZ hπ hH
    (hτ.mono hZO) (hδ.mono hZO) (fun x hx => hchart x.2 hx.2 x.1 hx.1)
  obtain ⟨T,hT,hqT,hτphysical⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr k hk
  obtain ⟨R,hRsub,hR,hqR⟩ := _root_.mem_nhds_iff.mp hdphysical
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let W := ((V ∩ T) ∩ R) ∩ P ⁻¹' Z
  refine ⟨parametricCosinePrimitive H τ d,Ω,Z,W,hΩ,hconv,hangle',hZ,hqZ,
    ((hV.inter hT).inter hR).inter (hZ.preimage hP),⟨⟨⟨hqV,hqT⟩,hqR⟩,hqZ⟩,hspec.1,hspec.2.1,?_⟩
  intro p hp
  refine ⟨hp.2,?_⟩
  intro θ hθ
  have hτp : τ (P p) = (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ) := (hτphysical p hp.1.1.2).1
  have hδp : d (P p) = (hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ) := hRsub hp.1.2
  unfold parametricCosinePrimitive parametricConvexPrimitive hillAbelianCosinePrimitive
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  have hθt : (Real.pi : ℂ)+(t : ℂ)*(θ-(Real.pi : ℂ)) ∈ Ω := by
    have hc := hconv.lineMap_mem hπ hθ ht'
    simpa only [AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using hc
  dsimp only [parametricCosineNumerator]
  congr 1
  change H (cosineGapPoint (τ (P p)) (d (P p)) _,P p) = _
  have hz := (hchart (P p) hp.2 _ hθt).1
  rw [((hHphysical p hp.1.1.1).2 _ hz).2]
  rw [hτp,hδp]
  simp only [hillAbelianCosineDifferential,mul_div_assoc]

end NLS.KdV
