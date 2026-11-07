import NLS.KdV.HillMiuraJointContourIntegrands
import NLS.ZakharovShabat.SourceIndexedHigherActionFixedCircle

/-! One genuine action cotangent circle is valid on a full native
complex source ball. It is constructed from actual indexed-action
circles, identified on the real form and continued by full source
analyticity. The constant Miura energy shift is retained. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillHminusMiuraActionBall

theorem fderiv_action_fixed_circle_of_source_gradient (B : HillHminusMiuraActionBall)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ B.source) (a : ℂ) (R : ℝ)
    (hJ : AnalyticAt ℂ (sourceIndexedHigherAction (by norm_num) (by norm_num) (n:ℤ) 1) (B.diracSource q))
    (hgradient : ∀ v : CoeffPair 2,
      (fderiv ℂ (sourceIndexedHigherAction (by norm_num) (by norm_num) (n:ℤ) 1) (B.diracSource q)) v =
        -(Real.pi:ℂ)⁻¹*(∮ z in C(a,R), z*
          (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalDiscriminant (by norm_num)
            (periodOnePotential ψ) z) (B.diracSource q)) v /
              sourceCanonicalRoot (by norm_num) (by norm_num) (B.diracSource q) z))
    (hR : 0 ≤ R) (h : PeriodOneHminusOne) :
    (fderiv ℂ (hillHminusCanonicalAction n) q) h =
      -(2*(Real.pi:ℂ)⁻¹)*(∮ z in C(a,R), z*hillHminusDiscriminantCotangent
        (z^2-(B.shift:ℂ)) q h /
          sourceCanonicalRoot (by norm_num) (by norm_num) (B.diracSource q) z) := by
  have hv := (B.analytic_diracSource q hq).differentiableAt
  have hd := hJ.differentiableAt.comp q hv
  have hc := (hJ.differentiableAt.hasFDerivAt.comp q hv.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hd hc
  have he : hillHminusCanonicalAction n =ᶠ[𝓝 q]
      (fun p => 2*sourceIndexedHigherAction (by norm_num) (by norm_num) (n:ℤ) 1 (B.diracSource p)) := by
    filter_upwards [B.source_open.mem_nhds hq] with p hp
    exact B.canonical_action_eq n p hp
  have hp : (fderiv ℂ (hillHminusCanonicalAction n) q) h =
      2*((fderiv ℂ (sourceIndexedHigherAction (by norm_num) (by norm_num) (n:ℤ) 1)
        (B.diracSource q)) ((fderiv ℂ B.diracSource q) h)) := by
    rw [he.fderiv_eq,fderiv_const_mul hd (2:ℂ),hc]
    simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply]
  rw [hp,hgradient]
  have hi : (∮ z in C(a,R), z*
      (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalDiscriminant (by norm_num) (periodOnePotential ψ) z)
        (B.diracSource q)) ((fderiv ℂ B.diracSource q) h) /
        sourceCanonicalRoot (by norm_num) (by norm_num) (B.diracSource q) z) =
      ∮ z in C(a,R), z*hillHminusDiscriminantCotangent (z^2-(B.shift:ℂ)) q h /
        sourceCanonicalRoot (by norm_num) (by norm_num) (B.diracSource q) z := by
    apply circleIntegral.integral_congr hR
    intro z _
    dsimp only [diracSource]
    exact congrArg (fun v : ℂ => z*v/sourceCanonicalRoot (by norm_num) (by norm_num) (B.diracSource q) z)
      (fderiv_liftedMiuraDiscriminant_eq_native B.source B.source_open B.lift B.lift_analytic
        (B.shift:ℂ) B.image q hq z h)
  rw [hi]
  ring

theorem exists_fixed_action_gradient_contour (B : HillHminusMiuraActionBall)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ W : Set (CoeffPair 2), IsOpen (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W) ∧
      AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct (by norm_num) (by norm_num))
        (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W) ∧
      ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧
        ball q r ⊆ B.source ∩ hillHminusCanonicalDirichletDomain ∧
        (∀ p ∈ ball q r, ∀ z ∈ sphere a R, (z,p) ∈ B.rootJointDomain W) ∧
        ∀ p ∈ ball q r, fderiv ℂ (hillHminusCanonicalAction n) p =
          -(2*(Real.pi:ℂ)⁻¹) •
            (∮ z in C(a,R), hillMiuraActionCotangentIntegrand p (B.lift p) (B.shift:ℂ) z) := by
  obtain ⟨U,hU,hqU,W,hDW,hroot,hUW,a,R,hR,hcircle,hgradient⟩ :=
    exists_sourceIndexedHigherAction_fixed_gradient_circle (by norm_num) (by norm_num) (n:ℤ)
      (B.diracSource q) (B.diracSource_real q hq hr)
  have hV : IsOpen (B.source ∩ B.diracSource ⁻¹' U) :=
    B.analytic_diracSource.continuousOn.isOpen_inter_preimage B.source_open hU
  obtain ⟨r,hrpos,hsub⟩ := Metric.mem_nhds_iff.mp
    ((hV.inter isOpen_hillHminusCanonicalDirichletDomain).mem_nhds
      ⟨⟨hq,hqU⟩,real_mem_hillHminusCanonicalDirichletDomain q hr⟩)
  have hsource : ball q r ⊆ B.source ∩ hillHminusCanonicalDirichletDomain :=
    fun p hp => ⟨(hsub hp).1.1,(hsub hp).2⟩
  have hc : ∀ p ∈ ball q r, ∀ z ∈ sphere a R, (z,p) ∈ B.rootJointDomain W := by
    intro p hp z hz
    exact ⟨⟨mem_univ _,(hsource hp).1⟩,hUW (hsub hp).1.2,hcircle (B.diracSource p) (hsub hp).1.2 hz⟩
  have hcontour : AnalyticOnNhd ℂ (fun p =>
      ∮ z in C(a,R), hillMiuraActionCotangentIntegrand p (B.lift p) (B.shift:ℂ) z) (ball q r) :=
    analyticOnNhd_circleIntegral_of_jointAnalytic _ (B.isOpen_rootJointDomain W hDW)
      (B.analytic_actionCotangentIntegrand_joint W hroot) a R hR.le isOpen_ball hc
  have haction : ball q r ⊆ hillHminusCanonicalActionDomain :=
    fun p hp => mem_iUnion.mpr ⟨B,(hsource hp).1⟩
  have hreal (p : PeriodOneHminusOne) (hp : p ∈ ball q r) (hpr : IsRealPeriodOneHminusOne p)
      (h : PeriodOneHminusOne) :
      (fderiv ℂ (hillHminusCanonicalAction n) p) h =
        -(2*(Real.pi:ℂ)⁻¹)*
          (∮ z in C(a,R), hillMiuraActionCotangentIntegrand p (B.lift p) (B.shift:ℂ) z) h := by
    have hg := hgradient (B.diracSource p) (hsub hp).1.2 (B.diracSource_real p (hsource hp).1 hpr) 1
    have hpoint := B.fderiv_action_fixed_circle_of_source_gradient n p (hsource hp).1 a R hg.1
      (by simpa only [pow_one] using hg.2) hR.le h
    have hci := circleIntegrable_hillMiuraActionCotangentIntegrand p (B.lift p) (B.shift:ℂ) a R hR.le
      (fun z hz => (hc p hp z hz).2.2)
    have hev := NLS.ComplexAnalysis.map_circleIntegral (ContinuousLinearMap.apply ℂ ℂ h) hci
    change (∮ z in C(a,R), hillMiuraActionCotangentIntegrand p (B.lift p) (B.shift:ℂ) z) h = _ at hev
    rw [hev]
    change (fderiv ℂ (hillHminusCanonicalAction n) p) h = -(2*(Real.pi:ℂ)⁻¹)*
      (∮ z in C(a,R), (z/sourceCanonicalRoot (by norm_num) (by norm_num) (B.diracSource p) z)*
        hillHminusDiscriminantCotangent (z^2-(B.shift:ℂ)) p h)
    simpa only [div_mul_eq_mul_div] using hpoint
  refine ⟨W,hDW,hroot,a,R,hR,r,hrpos,hsource,hc,?_⟩
  intro p hp
  ext h
  have he := analytic_eqOn_of_real_periodOneHminus (ball q r) isOpen_ball
    (convex_ball q r).isPreconnected ⟨q,mem_ball_self hrpos,hr⟩
    (fun b => (fderiv ℂ (hillHminusCanonicalAction n) b) h)
    (fun b => -(2*(Real.pi:ℂ)⁻¹)*
      (∮ z in C(a,R), hillMiuraActionCotangentIntegrand b (B.lift b) (B.shift:ℂ) z) h)
    ((ContinuousLinearMap.apply ℂ ℂ h).comp_analyticOnNhd
      ((analyticOnNhd_hillHminusCanonicalAction n).mono haction).fderiv)
    (analyticOnNhd_const.mul ((ContinuousLinearMap.apply ℂ ℂ h).comp_analyticOnNhd hcontour))
    (fun b hb hbr => hreal b hb hbr h)
  exact he hp

end NLS.KdV.HillHminusMiuraActionBall
