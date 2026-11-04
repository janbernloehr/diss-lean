import NLS.KdV.HillUniformDeflatedGapCharts
import NLS.KdV.HillAbelianOpenGapPrimitiveCharts
import NLS.ComplexAnalysis.ParametricPrimitiveBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- On each original open gap, the actual cosine primitives have common
bounded analytic charts of order inverse differential index. -/
theorem exists_hillAbelianCosinePrimitive_uniform_open_gap_charts
    (k : ℕ) (hk : 1≤k) (hgap : hillRealGapHalfLength q hq hr k≠0) :
    ∃ δ M : ℝ, ∃ Ω : Set ℂ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<M ∧ IsOpen Ω ∧ Convex ℝ Ω ∧
      segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ)⊆Ω ∧
      (∀ θ∈Ω, ‖θ‖<Real.pi+1) ∧ IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : 1≤n, ∃ F : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ F (Ω ×ˢ ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ p : Coeff 2, F ((Real.pi : ℂ),p)=0) ∧
        (∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ∀ θ∈Ω, ‖F (θ,p)‖≤M/(n : ℝ)) ∧
        ∀ p∈V, ∀ θ∈Ω, F (θ,SpectralWeight.one.toCoeff p.val)=
          hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k θ := by
  obtain ⟨δg,C,E,Vg,hδg,hC,hE,hVg,hgapE,hqVg,_,hcharts⟩ :=
    exists_hillDeflatedNormalizedDifferential_uniform_gap_charts q hq hr h0q h0r k hk
  obtain ⟨A,_,hqA,hMid,_,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  obtain ⟨d,hd,hd0,_,hdphysical⟩ := exists_hillGapHalfLength_analytic_extension q hq hr k hk hgap
  let τ := hillLocalGapMidpoint q hq hr k
  let U := ball (SpectralWeight.one.toCoeff q) δg
  let O := U∩({p | AnalyticAt ℂ τ p}∩{p | AnalyticAt ℂ d p})
  have hO : IsOpen O := isOpen_ball.inter ((isOpen_analyticAt ℂ τ).inter (isOpen_analyticAt ℂ d))
  have hqO : SpectralWeight.one.toCoeff q∈O := ⟨mem_ball_self hδg,hMid _ hqA,hd⟩
  have hτ : AnalyticOnNhd ℂ τ O := fun _ hp => hp.2.1
  have hd' : AnalyticOnNhd ℂ d O := fun _ hp => hp.2.2
  have hMid0 := (hillLocalGapSymmetricData_eq_physical_of_geometry q hq hr q hq hr k hk
    (hillRealGapContour_band_bounds q hq hr k hk) (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk)).1
  have hgeom := hillRealGapContour_geometry q hq hr k hk
  have hl : τ (SpectralWeight.one.toCoeff q)-d (SpectralWeight.one.toCoeff q)=
      (hillRealLabels q hq hr (2*k-1) : ℂ) := by
    dsimp only [τ]
    rw [hMid0,hd0,←ofReal_sub,hgeom.2.2.1]
  have hu : τ (SpectralWeight.one.toCoeff q)+d (SpectralWeight.one.toCoeff q)=
      (hillRealLabels q hq hr (2*k) : ℂ) := by
    dsimp only [τ]
    rw [hMid0,hd0,←ofReal_add,hgeom.2.2.2.1]
  obtain ⟨Z,Ω0,hZ,hqZ,hZO,hΩ0,hconv0,hangle0,hchart⟩ := exists_local_parametricCosine_chart_on_real_segment
    τ d O hO hτ hd' (E ×ˢ U) (hE.prod isOpen_ball) (SpectralWeight.one.toCoeff q) hqO (-Real.pi) Real.pi
    (by intro z hz;rw [hl,hu] at hz;exact ⟨hgapE hz,mem_ball_self hδg⟩)
  let Ω := Ω0∩ball (0 : ℂ) (Real.pi+1)
  have hΩ : IsOpen Ω := hΩ0.inter isOpen_ball
  have hconv : Convex ℝ Ω := hconv0.inter (convex_ball _ _)
  have hangle : segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ)⊆Ω := by
    have hends : ‖(Real.pi : ℂ)‖<Real.pi+1 := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      linarith
    have hball := (convex_ball (0 : ℂ) (Real.pi+1)).segment_subset
      (show -(Real.pi : ℂ)∈ball (0 : ℂ) (Real.pi+1) by simpa only [mem_ball,dist_zero_right,norm_neg] using hends)
      (show (Real.pi : ℂ)∈ball (0 : ℂ) (Real.pi+1) by simpa only [mem_ball,dist_zero_right] using hends)
    intro θ hθ
    exact ⟨hangle0 (by simpa only [ofReal_neg] using hθ),hball hθ⟩
  have hπ : (Real.pi : ℂ)∈Ω := hangle (right_mem_segment ℝ _ _)
  obtain ⟨δ,hδ,hδZ⟩ := Metric.mem_nhds_iff.mp (hZ.mem_nhds hqZ)
  have hsource (p : Coeff 2) (hp : p∈ball (SpectralWeight.one.toCoeff q) δ) : p∈U := (hZO (hδZ hp)).1
  obtain ⟨T,hT,hqT,hτphysical⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr k hk
  obtain ⟨R,hRsub,hR,hqR⟩ := _root_.mem_nhds_iff.mp hdphysical
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let V := ((Vg∩T)∩R)∩P ⁻¹' ball (SpectralWeight.one.toCoeff q) δ
  have hV : IsOpen V := ((hVg.inter hT).inter hR).inter (isOpen_ball.preimage hP)
  have hqV : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V := by
    refine ⟨⟨⟨hqVg,hqT⟩,hqR⟩,?_⟩
    change SpectralWeight.one.toCoeff q∈ball (SpectralWeight.one.toCoeff q) δ
    exact mem_ball_self hδ
  let M := (2*Real.pi+1)*C
  have hM : 0<M := by dsimp only [M];positivity
  refine ⟨δ,M,Ω,V,hδ,hM,hΩ,hconv,hangle,(fun θ hθ => by simpa only [mem_ball,dist_zero_right] using hθ.2),hV,hqV,
    (fun p hp => hp.2),?_⟩
  intro n hn
  obtain ⟨H,hH,hHb,hHphysical⟩ := hcharts n hn
  have hchart' (x : ℂ × Coeff 2) (hx : x∈Ω ×ˢ ball (SpectralWeight.one.toCoeff q) δ) :
      (cosineGapPoint (τ x.2) (d x.2) x.1,x.2)∈E ×ˢ U := hchart x.2 (hδZ hx.2) x.1 hx.1.1
  have hspec := parametricCosinePrimitive_spec H τ d (E ×ˢ U) Ω (ball (SpectralWeight.one.toCoeff q) δ)
    hΩ hconv isOpen_ball hπ hH (fun p hp => hτ p (hZO (hδZ hp)))
    (fun p hp => hd' p (hZO (hδZ hp))) hchart'
  refine ⟨parametricCosinePrimitive H τ d,hspec.1,hspec.2.1,?_,?_⟩
  · intro p hp θ hθ
    have hb := norm_parametricConvexPrimitive_le (parametricCosineNumerator H τ d) (Real.pi : ℂ) θ p Ω
      (C/(n : ℝ)) hconv hπ hθ (fun w hw => hHb p (hsource p hp) _ (hchart' (w,p) ⟨hw,hp⟩).1)
    apply hb.trans
    have hθbound : ‖θ‖<Real.pi+1 := by simpa only [mem_ball,dist_zero_right] using hθ.2
    have hlen : ‖θ-(Real.pi : ℂ)‖≤2*Real.pi+1 := by
      have hh := norm_sub_le θ (Real.pi : ℂ)
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] at hh
      linarith
    apply (mul_le_mul_of_nonneg_right hlen (by positivity : 0≤C/(n : ℝ))).trans_eq
    dsimp only [M]
    ring
  · intro p hp θ hθ
    have hτp : τ (P p)=(hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ) := (hτphysical p hp.1.1.2).1
    have hdp : d (P p)=(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ) := hRsub hp.1.2
    unfold parametricCosinePrimitive parametricConvexPrimitive hillAbelianCosinePrimitive
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hθt : (Real.pi : ℂ)+(t : ℂ)*(θ-(Real.pi : ℂ))∈Ω := by
      have hh := hconv.lineMap_mem hπ hθ ht'
      simpa only [AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using hh
    dsimp only [parametricCosineNumerator]
    congr 1
    change H (cosineGapPoint (τ (P p)) (d (P p)) _,P p)=_
    have hz := (hchart' (_,P p) ⟨hθt,hp.2⟩).1
    rw [(hHphysical p hp.1.1.1 _ hz).2,hτp,hdp]
    simp only [hillAbelianCosineDifferential,mul_div_assoc]

end NLS.KdV
