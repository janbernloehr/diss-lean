import NLS.KdV.HillLocalAbelianPrimitives
import NLS.ComplexAnalysis.ParametricPolygonalIntegral

/-! Actual polygonal Abelian integrals and continuation to a moving
energy endpoint on a joint physical root box. The admissible source
domain is OPEN and common BEFORE ALL numerator indices. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusAbelianPathDomain (k : ℕ) (v : ℕ → ℂ) : Set PeriodOneHminusOne :=
  parametricPolygonalDomain k v hillHminusCanonicalEnergyRootDomain

def hillHminusAbelianPathIntegral (n : ℕ+) (k : ℕ) (v : ℕ → ℂ) : PeriodOneHminusOne → ℂ :=
  parametricPolygonalIntegral (hillHminusCanonicalEnergyDifferential n) k v

theorem isOpen_hillHminusAbelianPathDomain (k : ℕ) (v : ℕ → ℂ) :
    IsOpen (hillHminusAbelianPathDomain k v) :=
  isOpen_parametricPolygonalDomain k v _ isOpen_hillHminusCanonicalEnergyRootDomain

theorem analyticOnNhd_hillHminusAbelianPathIntegral (n : ℕ+) (k : ℕ) (v : ℕ → ℂ) :
    AnalyticOnNhd ℂ (hillHminusAbelianPathIntegral n k v) (hillHminusAbelianPathDomain k v) :=
  analyticOnNhd_parametricPolygonalIntegral _ k v _ isOpen_hillHminusCanonicalEnergyRootDomain
    (analyticOnNhd_hillHminusCanonicalEnergyDifferential n)

theorem real_mem_hillHminusAbelianPathDomain_of_nonreal_segments (k : ℕ) (v : ℕ → ℂ)
    (hpath : ∀ i : Fin k, ∀ E ∈ segment ℝ (v i.val) (v (i.val+1)), E.im ≠ 0)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) : q ∈ hillHminusAbelianPathDomain k v := by
  intro i E hE
  exact nonreal_mem_hillHminusCanonicalEnergyRootDomain E (hpath i E hE) q hr

theorem exists_common_complex_abelian_path_ball (k : ℕ) (v : ℕ → ℂ) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusAbelianPathDomain k v) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ hillHminusAbelianPathDomain k v ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusAbelianPathIntegral n k v) (ball q r) := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (isOpen_hillHminusAbelianPathDomain k v) q hq
  exact ⟨r,hr,hball,fun n => (analyticOnNhd_hillHminusAbelianPathIntegral n k v).mono hball⟩

def hillHminusAbelianPathContinuation (B : HillHminusEnergyRootBox) (n : ℕ+) (k : ℕ)
    (v : ℕ → ℂ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillHminusAbelianPathIntegral n k v t.2+B.abelianPrimitive n t-B.abelianPrimitive n (v k,t.2)

theorem analyticOnNhd_hillHminusAbelianPathContinuation (B : HillHminusEnergyRootBox)
    (k : ℕ) (v : ℕ → ℂ) (hb : v k ∈ ball B.energyCenter B.energyRadius) (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusAbelianPathContinuation B n k v)
      (B.domain ∩ (univ ×ˢ hillHminusAbelianPathDomain k v)) := by
  intro t ht
  have hpath := (analyticOnNhd_hillHminusAbelianPathIntegral n k v t.2 ht.2.2).comp
    (f := fun y : ℂ × PeriodOneHminusOne => y.2) analyticAt_snd
  have hlast := (B.analytic_abelianPrimitive n (v k,t.2) ⟨hb,ht.1.2⟩).comp
    (f := fun y : ℂ × PeriodOneHminusOne => (v k,y.2)) (analyticAt_const.prod analyticAt_snd)
  exact (hpath.add (B.analytic_abelianPrimitive n t ht.1)).sub hlast

theorem hillHminusAbelianPathContinuation_at_terminal (B : HillHminusEnergyRootBox)
    (n : ℕ+) (k : ℕ) (v : ℕ → ℂ) (q : PeriodOneHminusOne) :
    hillHminusAbelianPathContinuation B n k v (v k,q) = hillHminusAbelianPathIntegral n k v q := by
  unfold hillHminusAbelianPathContinuation
  ring

theorem hasDerivAt_hillHminusAbelianPathContinuation (B : HillHminusEnergyRootBox)
    (n : ℕ+) (k : ℕ) (v : ℕ → ℂ) (E : ℂ) (q : PeriodOneHminusOne) (ht : (E,q) ∈ B.domain) :
    HasDerivAt (fun z => hillHminusAbelianPathContinuation B n k v (z,q))
      (hillHminusCanonicalEnergyDifferential n (E,q)) E := by
  exact ((B.hasDerivAt_abelianPrimitive n E q ht).const_add
    (hillHminusAbelianPathIntegral n k v q)).sub_const (B.abelianPrimitive n (v k,q))

theorem hillHminusAbelianPathContinuation_eq_appended_segment (B : HillHminusEnergyRootBox)
    (n : ℕ+) (k : ℕ) (v : ℕ → ℂ) (hb : v k ∈ ball B.energyCenter B.energyRadius)
    (E : ℂ) (q : PeriodOneHminusOne) (ht : (E,q) ∈ B.domain) :
    hillHminusAbelianPathContinuation B n k v (E,q) = hillHminusAbelianPathIntegral n k v q+
      ∫ᶜ z in Path.segment (v k) E, holomorphicOneForm (fun w => hillHminusCanonicalEnergyDifferential n (w,q)) z := by
  have hInt := curveIntegral_segment_eq_sub_of_primitive
    (fun z => hillHminusCanonicalEnergyDifferential n (z,q)) (fun z => B.abelianPrimitive n (z,q))
    (ball B.energyCenter B.energyRadius) (B.analytic_energyDifferential n q ht.2).continuousOn
    (fun z hz => B.hasDerivAt_abelianPrimitive n z q ⟨hz,ht.2⟩) (v k) E
    ((convex_ball B.energyCenter B.energyRadius).segment_subset hb ht.1)
  rw [hInt,hillHminusAbelianPathContinuation]
  ring

theorem analyticAt_hillHminusAbelianPathContinuation_moving_terminal (B : HillHminusEnergyRootBox)
    (n : ℕ+) (k : ℕ) (v : ℕ → ℂ) (hb : v k ∈ ball B.energyCenter B.energyRadius)
    (μ : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) (hμ : AnalyticAt ℂ μ q)
    (hq : q ∈ B.source ∩ hillHminusAbelianPathDomain k v)
    (hμq : μ q ∈ ball B.energyCenter B.energyRadius) :
    AnalyticAt ℂ (fun y => hillHminusAbelianPathContinuation B n k v (μ y,y)) q :=
  (analyticOnNhd_hillHminusAbelianPathContinuation B k v hb n (μ q,q)
    ⟨⟨hμq,hq.1⟩,mem_univ _,hq.2⟩).comp (f := fun y => (μ y,y)) (hμ.prod analyticAt_id)

theorem hillHminusAbelianPathIntegral_eq_physical_of_real (n : ℕ+) (k : ℕ) (v : ℕ → ℂ)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hpath : ∀ i : Fin k, ∀ E ∈ segment ℝ (v i.val) (v (i.val+1)), E.im ≠ 0) :
    hillHminusAbelianPathIntegral n k v q = ∑ i : Fin k,
      ∫ᶜ z in Path.segment (v i.val) (v (i.val+1)),
        holomorphicOneForm (fun E => hillHminusCanonicalPsi n (E,q)/hillHminusContinuedRoot (E,q)) z := by
  unfold hillHminusAbelianPathIntegral parametricPolygonalIntegral
  apply Finset.sum_congr rfl
  intro i _
  apply curveIntegral_holomorphicOneForm_congr_interior
  intro t ht
  rw [Path.extend_apply _ ⟨ht.1.le,ht.2.le⟩]
  exact hillHminusCanonicalEnergyDifferential_eq_physical_of_real n _
    (hpath i _ (lineMap_mem_segment ℝ _ _ ⟨ht.1.le,ht.2.le⟩)) q hr

theorem exists_common_abelian_path_continuation_chart (k : ℕ) (v : ℕ → ℂ)
    (q : PeriodOneHminusOne) (hpath : q ∈ hillHminusAbelianPathDomain k v)
    (hb : (v k,q) ∈ hillHminusCanonicalEnergyRootDomain) :
    ∃ B : HillHminusEnergyRootBox, v k ∈ ball B.energyCenter B.energyRadius ∧
      ∃ r : ℝ, 0 < r ∧ ball q r ⊆ B.source ∩ hillHminusAbelianPathDomain k v ∧
        ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusAbelianPathContinuation B n k v)
          (ball B.energyCenter B.energyRadius ×ˢ ball q r) ∧
          ∀ t ∈ ball B.energyCenter B.energyRadius ×ˢ ball q r,
            HasDerivAt (fun E => hillHminusAbelianPathContinuation B n k v (E,t.2))
              (hillHminusCanonicalEnergyDifferential n t) t.1 := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hb
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp
    (isOpen_ball.inter (isOpen_hillHminusAbelianPathDomain k v)) q ⟨hB.2,hpath⟩
  refine ⟨B,hB.1,r,hr,hball,?_⟩
  intro n
  refine ⟨(analyticOnNhd_hillHminusAbelianPathContinuation B k v hB.1 n).mono ?_,?_⟩
  · intro t ht
    exact ⟨⟨ht.1,(hball ht.2).1⟩,mem_univ _,(hball ht.2).2⟩
  · intro t ht
    exact hasDerivAt_hillHminusAbelianPathContinuation B n k v t.1 t.2 ⟨ht.1,(hball ht.2).1⟩

end NLS.KdV
