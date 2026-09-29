import NLS.ZakharovShabat.SourcePsiComplexChartCompatibility
import NLS.ZakharovShabat.SourcePsiComplexJacobianNeighborhood
import NLS.ZakharovShabat.SourcePsiGlobalEquationTaylorTruncation
import NLS.ComplexAnalysis.GlueHolomorphicCharts

/-!
# Glued analytic psi equations with common inverse bounds

Joint ball charts at one real source agree on overlaps, even when
their root centers and contour families differ. They therefore define
one equation for each deleted index. Its scalar contour formulas give
Banach analyticity on the common canonical-root source domain. The
actual partial derivatives retain both full and deleted inverse bounds
on a single convex full-space neighborhood of the entire gap product.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal Pointwise
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_sourcePsi_gluedEquation_neighborhood
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ Convex ℝ U ∧
      sourcePeriodicGapRootSet hp hp1 φ ×ˢ {φ} ⊆ U ∧
      ∃ V : (n : ℤ) → Set (DeletedCoeff p n × CoeffPair p),
        (∀ n, IsOpen (V n)) ∧
        (∀ t ∈ U, ∀ n, (Coeff.deleteCoordinateTo n t.1,t.2) ∈ V n) ∧
      ∃ F : (n : ℤ) → DeletedCoeff p n × CoeffPair p → DeletedCoeff p n,
        (∀ n, AnalyticOnNhd ℂ (F n) (V n)) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ∀ q ∈ V n,
        (∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
          sourcePsiRealCenteredContourFamily hp hp1 q.2 c R ∧
          ∀ m, (F n q : Coeff p) m =
            sourcePsiEquationCoordinate hp hp1 n m (q.1 : Coeff p) q.2 (c m) (R m)) ∧
        (∃ S : Coeff p →L[ℂ] Coeff p,
          (Coeff.deletedJacobianExtension n (fderiv ℂ (fun b => F n (b,q.2)) q.1)).comp S =
            ContinuousLinearMap.id ℂ (Coeff p) ∧
          S.comp (Coeff.deletedJacobianExtension n (fderiv ℂ (fun b => F n (b,q.2)) q.1)) =
            ContinuousLinearMap.id ℂ (Coeff p) ∧ ‖S‖ ≤ M) ∧
        (∃ S : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
          (fderiv ℂ (fun b => F n (b,q.2)) q.1).comp S = ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
          S.comp (fderiv ℂ (fun b => F n (b,q.2)) q.1) = ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
          ‖S‖ ≤ M) := by
  classical
  obtain ⟨M,hM,hlocal⟩ := exists_uniform_local_sourcePsi_complexJacobian_inverses hp hp1 φ hφ
  choose c R hfamily δ L hδ hL hcharts using hlocal
  obtain ⟨W,hWopen,hWconnected,hrealW,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  let B : (n : ℤ) → sourcePeriodicGapRootSet hp hp1 φ → Set (DeletedCoeff p n × CoeffPair p) :=
    fun n a => ball (Coeff.deleteCoordinateTo n a.val,φ) (δ a)
  let f : (n : ℤ) → sourcePeriodicGapRootSet hp hp1 φ →
      DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun n a q => sourcePsiSelectedEquationSequence hp hp1 n (c a n) (R a n) q.1 q.2
  have hcompat (n : ℤ) (a b : sourcePeriodicGapRootSet hp hp1 φ) :
      EqOn (f n a) (f n b) (B n a ∩ B n b) :=
    sourcePsiSelectedEquationSequence_eqOn_ball_charts hp hp1 n
      (Coeff.deleteCoordinateTo n a.val) (Coeff.deleteCoordinateTo n b.val) φ hφ (δ a) (δ b)
      (c a n) (c b n) (R a n) (R b n)
      (hcharts a n).1.2.2.2 (hcharts b n).1.2.2.2 (hcharts a n).1.1 (hcharts b n).1.1
  let G : (n : ℤ) → DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun n => NLS.ComplexAnalysis.glueHolomorphicCharts (B n) (f n)
  let V : (n : ℤ) → Set (DeletedCoeff p n × CoeffPair p) :=
    fun n => (⋃ a, B n a) ∩ {q | q.2 ∈ W}
  have hVopen (n : ℤ) : IsOpen (V n) :=
    (isOpen_iUnion (fun a => isOpen_ball)).inter (hWopen.preimage continuous_snd)
  have hGlocal (n : ℤ) (a : sourcePeriodicGapRootSet hp hp1 φ) : EqOn (G n) (f n a) (B n a) :=
    NLS.ComplexAnalysis.glueHolomorphicCharts_eq_on (B n) (f n) (hcompat n) a
  have hGdiff (n : ℤ) : DifferentiableOn ℂ (G n) (V n) :=
    (NLS.ComplexAnalysis.differentiableOn_glueHolomorphicCharts (B n) (f n)
      (fun a => isOpen_ball) (hcompat n) (fun a => (hcharts a n).1.1)).mono inter_subset_left
  have hGanalytic (n : ℤ) : AnalyticOnNhd ℂ (G n) (V n) := by
    have hscalar (m : ℤ) : AnalyticOnNhd ℂ (fun q => (G n q : Coeff p) m) (V n) := by
      intro q hq
      obtain ⟨a,ha⟩ := mem_iUnion.mp hq.1
      have hgeom := (hcharts a n).1.2.2.2 q ha
      have hraw := analyticAt_sourcePsiEquationCoordinate_of_contour_domain hp hp1 n m
        (q.1 : Coeff p) q.2 (c a n m) (R a n m) (hgeom.2 m).1.le W hq.2
          (hdata n).1 (hdata n).2 (hgeom.2 m).2.2.2
      have hH : AnalyticAt ℂ
          (fun t : DeletedCoeff p n × CoeffPair p => ((t.1 : Coeff p),t.2)) q :=
        ((((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL.analyticAt q.1).comp
          analyticAt_fst).prod analyticAt_snd)
      have hrawQ := hraw.comp (f := fun t : DeletedCoeff p n × CoeffPair p =>
        ((t.1 : Coeff p),t.2)) hH
      have heq : (fun t : DeletedCoeff p n × CoeffPair p => (G n t : Coeff p) m)
          =ᶠ[𝓝 q] (fun t => sourcePsiEquationCoordinate hp hp1 n m
            (t.1 : Coeff p) t.2 (c a n m) (R a n m)) := by
        filter_upwards [isOpen_ball.mem_nhds ha] with t ht
        rw [hGlocal n a ht]
        exact (hcharts a n).1.2.1 t ht m
      exact hrawQ.congr heq.symm
    have hcoeff : AnalyticOnNhd ℂ (fun q => (G n q : Coeff p)) (V n) :=
      NLS.Coeff.analyticOnNhd_of_coordinatewise_of_continuousOn
        (fun q => (G n q : Coeff p)) (hVopen n) hscalar
        (continuous_subtype_val.comp_continuousOn (hGdiff n).continuousOn)
    have hproject := (Coeff.deleteCoordinateTo (p := p) n).comp_analyticOnNhd hcoeff
    apply hproject.congr (hVopen n)
    intro q _
    apply Subtype.ext
    exact (Coeff.deleteCoordinate_eq_self_iff n (G n q : Coeff p)).2 (G n q).property
  let U : Set (Coeff p × CoeffPair p) :=
    (⋃ a : sourcePeriodicGapRootSet hp hp1 φ, ball (a.val,φ) (δ a)) ∩ {t | t.2 ∈ W}
  have hUopen : IsOpen U :=
    (isOpen_iUnion (fun a => isOpen_ball)).inter (hWopen.preimage continuous_snd)
  have hbase : sourcePeriodicGapRootSet hp hp1 φ ×ˢ {φ} ⊆ U := by
    rintro ⟨a,ψ⟩ ⟨ha,hψ⟩
    have hψφ : ψ = φ := mem_singleton_iff.mp hψ
    subst ψ
    exact ⟨mem_iUnion.mpr ⟨⟨a,ha⟩,mem_ball_self (hδ ⟨a,ha⟩)⟩,hrealW hφ⟩
  have hprojection : ∀ t ∈ U, ∀ n, (Coeff.deleteCoordinateTo n t.1,t.2) ∈ V n := by
    intro t ht n
    obtain ⟨a,ha⟩ := mem_iUnion.mp ht.1
    refine ⟨mem_iUnion.mpr ⟨a,?_⟩,ht.2⟩
    have hproj : ‖Coeff.deleteCoordinateTo n t.1-Coeff.deleteCoordinateTo n a.val‖ ≤ ‖t.1-a.val‖ := by
      rw [← map_sub]
      simpa only [one_mul] using (Coeff.deleteCoordinateTo (p := p) n).le_of_opNorm_le
        (Coeff.norm_deleteCoordinateTo_le_one n) (t.1-a.val)
    rw [mem_ball,Prod.dist_eq]
    rw [mem_ball,Prod.dist_eq] at ha
    exact (max_le_max (by simpa only [dist_eq_norm] using hproj) le_rfl).trans_lt ha
  let K : Set (Coeff p × CoeffPair p) := sourcePeriodicGapRootSet hp hp1 φ ×ˢ {φ}
  have hK : IsCompact K := (isCompact_sourcePeriodicGapRootSet hp hp1 φ).prod
    (isCompact_singleton : IsCompact {φ})
  obtain ⟨ε,hε,htube⟩ := hK.exists_cthickening_subset_open hUopen hbase
  let U' := K + ball (0 : Coeff p × CoeffPair p) ε
  have hconvK : Convex ℝ K := (convex_sourcePeriodicGapRootSet hp hp1 φ).prod (convex_singleton φ)
  have hbase' : K ⊆ U' := by
    intro t ht
    exact mem_add.mpr ⟨t,ht,0,mem_ball_self hε,add_zero t⟩
  have hU'subset : U' ⊆ U := by
    intro t ht
    obtain ⟨k,hk,z,hz,rfl⟩ := mem_add.mp ht
    apply htube
    apply mem_cthickening_of_dist_le (k+z) k ε K hk
    rw [dist_eq_norm,add_sub_cancel_left]
    exact le_of_lt (by simpa only [mem_ball,dist_zero_right] using hz)
  refine ⟨U',isOpen_ball.add_left,hconvK.add (convex_ball 0 ε),hbase',V,hVopen,
    (fun t ht => hprojection t (hU'subset ht)),G,hGanalytic,M,hM,?_⟩
  intro n q hq
  obtain ⟨a,ha⟩ := mem_iUnion.mp hq.1
  have hnear : G n =ᶠ[𝓝 q] f n a :=
    NLS.ComplexAnalysis.glueHolomorphicCharts_eventuallyEq (B n) (f n)
      (fun a => isOpen_ball) (hcompat n) a q ha
  have hpair : Continuous (fun b : DeletedCoeff p n => (b,q.2)) := continuous_id.prodMk continuous_const
  have hrootEq : (fun b : DeletedCoeff p n => G n (b,q.2)) =ᶠ[𝓝 q.1]
      (fun b => f n a (b,q.2)) := (hpair.tendsto q.1).eventually hnear
  have hderiv : fderiv ℂ (fun b => G n (b,q.2)) q.1 =
      sourcePsiSelectedRootJacobian hp hp1 n (c a n) (R a n) q.1 q.2 := hrootEq.fderiv_eq (𝕜 := ℂ)
  obtain ⟨S,hQS,hSQ,hS⟩ := (hcharts a n).2 q ha
  obtain ⟨Sd,hQSd,hSdQ,hSd⟩ := Coeff.exists_deleted_inverse_of_extension_inverse n
    (sourcePsiSelectedRootJacobian hp hp1 n (c a n) (R a n) q.1 q.2) S hQS hSQ
  refine ⟨⟨c a n,R a n,(hcharts a n).1.2.2.2 q ha,?_⟩,?_,?_⟩
  · intro m
    rw [hGlocal n a ha]
    exact (hcharts a n).1.2.1 q ha m
  · rw [hderiv]
    exact ⟨S,hQS,hSQ,hS⟩
  · rw [hderiv]
    exact ⟨Sd,hQSd,hSdQ,hSd.trans hS⟩

end NLS.ZakharovShabat
