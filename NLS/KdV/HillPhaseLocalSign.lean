import NLS.KdV.HillPhaseOpenGap
import NLS.KdV.HillRealPeriodOneAffinePath
import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

noncomputable section
set_option autoImplicit false
open Set Complex Metric Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

/-- The COMPLETE ORIGINAL physical phase factor has its ACTUAL local
complex H-minus-one analytic extension at every open own gap, including
zero-sheet endpoints. The square-root sign is fixed by affine paths in
the original real source space, not by a choice of compatible norm. -/
theorem exists_originalFullPhaseFactor_hminus_analytic_open (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : ∀ a∈P.miura.domain, hillHminusRadicand a (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)
    (n : ℕ+) (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0) :
    ∃ ε : ℝ, 0<ε ∧ ∃ F : PeriodOneHminusOne → ℂ,
      AnalyticOnNhd ℂ F (ball (hillOriginalHminusSource q.val) ε) ∧
      ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val∈ball (hillOriginalHminusSource q.val) ε →
        F (hillOriginalHminusSource p.val)=hillOriginalFullPhaseFactor n p := by
  let a := hillOriginalHminusSource q.val
  let Φ := P.sourceFullPhaseSquare n
  let w := hillOriginalFullPhaseFactor n q
  have hqD := P.original_open_mem_sourceFullPhaseDomain q hq hreal (houtside _ hq.1) c hshift n hgap
  have hΦ := P.analytic_sourceFullPhaseSquare H n
  have hw : w≠0 := by
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    intro hz
    have h := hillDirichletCirclePhase_norm q.val q.property.1 q.property.2 n n.pos hgap
    rw [hz,norm_zero] at h
    exact zero_ne_one h
  have hsq0 : Φ a=w^2 := (P.originalFullPhaseFactor_sq_eq_source_open H hreal houtside c hshift n q hq hgap).symm
  let U : Set PeriodOneHminusOne := P.sourceFullPhaseDomain n ∩ prescribedSquareRootDomain Φ w
  have hU : IsOpen U :=
    (hΦ.continuousOn.div_const (w^2)).isOpen_inter_preimage
      (P.sourceFullPhaseDomain_open H n) Complex.isOpen_slitPlane
  have haU : a∈U := ⟨hqD,mem_prescribedSquareRootDomain Φ w hw a hsq0⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU a haU
  let F := prescribedSquareRoot Φ w
  have hF : AnalyticOnNhd ℂ F (ball a ε) := by
    intro b hb
    have hs : AnalyticAt ℂ Complex.sqrt (Φ b/w^2) :=
      Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds (hball hb).2)
    exact analyticAt_const.mul (hs.comp (f := fun x : PeriodOneHminusOne => Φ x/w^2)
      ((hΦ b (hball hb).1).div analyticAt_const (pow_ne_zero 2 hw)))
  have hFne (b : PeriodOneHminusOne) (hb : b∈ball a ε) : F b≠0 :=
    prescribedSquareRoot_ne_zero Φ w hw b (hball hb).2
  have hbase : F a=w := prescribedSquareRoot_base Φ w hw a hsq0
  refine ⟨ε,hε,F,hF,?_⟩
  intro p hp
  let σ := hillRealPeriodOneAffinePath q p
  have hσ : Continuous σ := continuous_hillRealPeriodOneAffinePath q p
  have hsrc : Continuous (fun t : ℝ => hillOriginalHminusSource (σ t).val) :=
    hillOriginalHminusSource.continuous.comp (continuous_subtype_val.comp hσ)
  have hσball (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : hillOriginalHminusSource (σ t).val∈ball a ε := by
    have he : hillOriginalHminusSource (σ t).val=
        AffineMap.lineMap a (hillOriginalHminusSource p.val) t := by
      simp only [σ,hillRealPeriodOneAffinePath,map_add,map_smul,map_sub,AffineMap.lineMap_apply_module']
      rfl
    rw [he]
    exact (convex_ball a ε).segment_subset (mem_ball_self hε) hp (lineMap_mem_segment ℝ _ _ ht)
  have hopen (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      hillRealGapHalfLength (σ t).val (σ t).property.1 (σ t).property.2 n≠0 :=
    P.original_gap_open_of_sourceFullPhaseDomain (σ t) n (hball (hσball t ht)).1 hreal
      (houtside _ (hball (hσball t ht)).1.1.1) c hshift
  have hGc : ContinuousOn (fun t : ℝ => hillOriginalFullPhaseFactor n (σ t)) (Icc 0 1) := by
    intro t ht
    exact ((continuousAt_hillOriginalFullPhaseFactor_open n (σ t) (hopen t ht)).comp hσ.continuousAt).continuousWithinAt
  have hFc : ContinuousOn (fun t : ℝ => F (hillOriginalHminusSource (σ t).val)) (Icc 0 1) := by
    intro t ht
    exact ((hF _ (hσball t ht)).continuousAt.comp
      (f := fun t : ℝ => hillOriginalHminusSource (σ t).val) hsrc.continuousAt).continuousWithinAt
  have hsq (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      hillOriginalFullPhaseFactor n (σ t)^2=F (hillOriginalHminusSource (σ t).val)^2 :=
    (P.originalFullPhaseFactor_sq_eq_source_open H hreal houtside c hshift n (σ t)
      (hball (hσball t ht)).1.1 (hopen t ht)).trans
      (prescribedSquareRoot_sq Φ w hw _).symm
  have h0 : hillOriginalFullPhaseFactor n (σ 0)=F (hillOriginalHminusSource (σ 0).val) := by
    simpa only [σ,hillRealPeriodOneAffinePath_zero] using hbase.symm
  have heq := isPreconnected_Icc.eq_of_sq_eq hGc hFc hsq
    (fun {t} ht => hFne _ (hσball t ht)) (show (0:ℝ)∈Icc 0 1 by norm_num) h0
  have h1 := heq (show (1:ℝ)∈Icc 0 1 by norm_num)
  simpa only [σ,hillRealPeriodOneAffinePath_one] using h1.symm

/-- At EVERY original real potential and open own gap, the COMPLETE
original phase factor has a complex H-minus-one analytic extension,
matching ALL original real potentials in an actual H-minus-one ball.
All source charts and the exact physical square-root sign are constructed. -/
theorem exists_hillOriginal_fullPhaseFactor_hminus_analytic_open
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0) :
    ∃ ε : ℝ, 0<ε ∧ ∃ F : PeriodOneHminusOne → ℂ,
      AnalyticOnNhd ℂ F (ball (hillOriginalHminusSource q.val) ε) ∧
      ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val∈ball (hillOriginalHminusSource q.val) ε →
        F (hillOriginalHminusSource p.val)=hillOriginalFullPhaseFactor n p := by
  obtain ⟨P,c,_,_,hshift,hqP,hreal,houtside,H⟩ :=
    exists_hillHminusPsiChart_real_form_outside_shift (hillOriginalHminusSource q.val)
      (hillOriginalHminusSource_real q.val q.property.2) 0
  exact P.exists_originalFullPhaseFactor_hminus_analytic_open H hreal houtside c hshift n q hqP hgap

end NLS.KdV.HillHminusPsiChart
