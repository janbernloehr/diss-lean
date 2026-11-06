import NLS.KdV.HillUniformOpenGapPrimitives
import NLS.KdV.HillGlobalRegularAnalytic

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
/-- Every fixed open gap has common analytic regular correction charts
around an arbitrary real source, with an actual inverse-index bound. -/
theorem exists_hillRegularAbelianCorrection_uniform_open_gap_charts
    (k : ℕ) (hk : 1≤k) (hgap : hillRealGapHalfLength q hq hr k≠0) :
    ∃ δ C : ℝ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<C ∧ IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : 1≤n, ∃ β : Coeff 2 → ℂ,
        AnalyticOnNhd ℂ β (ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ‖β p‖≤C/(n : ℝ)) ∧
        ∀ p∈V, β (SpectralWeight.one.toCoeff p.val)=
          hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk := by
  obtain ⟨δg,M,Ω,Vg,hδg,hM,hΩ,_,hangle,hangleBound,hVg,hqVg,_,hcharts⟩ :=
    exists_hillAbelianCosinePrimitive_uniform_open_gap_charts q hq hr h0q h0r k hk hgap
  obtain ⟨ε,e,hε,hε0,he,hterminal⟩ := exists_hillDirichlet_analytic_sheeted_angle q hq hr k hk hgap
  have hbaseΩ : ε (SpectralWeight.one.toCoeff q)∈Ω := by rw [hε0];exact hangle he
  have hsmall : {p : Coeff 2 | AnalyticAt ℂ ε p ∧ ε p∈Ω}∈𝓝 (SpectralWeight.one.toCoeff q) :=
    inter_mem ((isOpen_analyticAt ℂ ε).mem_nhds hε) (hε.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hbaseΩ))
  obtain ⟨r,hrpos,hrsmall⟩ := Metric.mem_nhds_iff.mp hsmall
  let δ := min δg r
  have hδ : 0<δ := lt_min hδg hrpos
  have hdg : δ≤δg := min_le_left _ _
  have hsrc (p : Coeff 2) (hp : p∈ball (SpectralWeight.one.toCoeff q) δ) :=
    hrsmall (ball_subset_ball (min_le_right _ _) hp)
  obtain ⟨W,hWsub,hW,hqW⟩ := _root_.mem_nhds_iff.mp hterminal
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let V := (Vg∩W)∩P ⁻¹' ball (SpectralWeight.one.toCoeff q) δ
  have hV : IsOpen V := (hVg.inter hW).inter (isOpen_ball.preimage hP)
  have hqV : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V := by
    refine ⟨⟨hqVg,hqW⟩,?_⟩
    change SpectralWeight.one.toCoeff q∈ball (SpectralWeight.one.toCoeff q) δ
    exact mem_ball_self hδ
  let L := 2*Real.pi+1
  let C := M+(k : ℝ)*L
  have hC : 0<C := by dsimp only [C,L];positivity
  refine ⟨δ,C,V,hδ,hC,hV,hqV,(fun p hp => hp.2),?_⟩
  intro n hn
  obtain ⟨F,hF,_,hFb,hFreal⟩ := hcharts n hn
  let β : Coeff 2 → ℂ := fun p => F (ε p,p)-(if k=n then 1 else 0)*(ε p-(Real.pi : ℂ))
  refine ⟨β,?_,?_,?_⟩
  · intro p hp
    have hεp := (hsrc p hp).1
    have hFp := (hF (ε p,p) ⟨(hsrc p hp).2,ball_subset_ball hdg hp⟩).comp
      (f := fun p : Coeff 2 => (ε p,p)) (hεp.prod analyticAt_id)
    exact hFp.sub (analyticAt_const.mul (hεp.sub analyticAt_const))
  · intro p hp
    have hlen : ‖ε p-(Real.pi : ℂ)‖≤L := by
      have hθ := hangleBound (ε p) (hsrc p hp).2
      have hh := norm_sub_le (ε p) (Real.pi : ℂ)
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] at hh
      dsimp only [L]
      linarith
    have hterm : ‖(if k=n then (1 : ℂ) else 0)*(ε p-(Real.pi : ℂ))‖≤(k : ℝ)*L/(n : ℝ) := by
      by_cases hkn : k=n
      · rw [if_pos hkn,one_mul,hkn]
        have hnR : (n : ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
        rw [mul_div_cancel_left₀ L hnR]
        exact hlen
      · rw [if_neg hkn,zero_mul,norm_zero]
        dsimp only [L]
        positivity
    change ‖F (ε p,p)-(if k=n then (1 : ℂ) else 0)*(ε p-(Real.pi : ℂ))‖≤_
    apply (norm_sub_le _ _).trans
    apply (add_le_add (hFb p (ball_subset_ball hdg hp) (ε p) (hsrc p hp).2) hterm).trans_eq
    dsimp only [C]
    ring
  · intro p hp
    have ht := hWsub hp.1.2
    have hreal : ε (P p)=((ε (P p)).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [ofReal_im] using (show (ε (P p)).im=0 from ht.2.1)
    have hpoint : cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
        (hillRealGapHalfLength p.val p.property.1 p.property.2 k) ((ε (P p)).re : ℂ)=
          (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) := by
      rw [←hreal]
      exact ht.2.2.1
    have hsin : Complex.sin ((ε (P p)).re : ℂ)=hillDirichletGapSine p.val p.property.1 p.property.2 k hk := by
      rw [←hreal]
      exact ht.2.2.2
    rw [hillRegularAbelianCorrection_eq_of_terminal p.val p.property.1 p.property.2 n k hn hk ht.1 _ hpoint hsin]
    change F (ε (P p),P p)-(if k=n then (1 : ℂ) else 0)*(ε (P p)-(Real.pi : ℂ))=_
    rw [hFreal p hp.1.1 (ε (P p)) (hsrc (P p) hp.2).2]
    change hillRegularAbelianPrimitive p.val p.property.1 p.property.2 n hn k (ε (P p))=
      hillRegularAbelianPrimitive p.val p.property.1 p.property.2 n hn k ((ε (P p)).re : ℂ)
    rw [hreal]
    simp only [ofReal_re]

end NLS.KdV
