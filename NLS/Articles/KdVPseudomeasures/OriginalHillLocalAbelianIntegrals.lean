import NLS.Articles.KdVPseudomeasures.OriginalHillCanonicalEnergySheets
import NLS.KdV.HillAbelianPathContinuation

/-! Actual local Abelian integrals, literal finite path integrals and
analytic moving-endpoint continuation for the original Hill
normalized differentials. These are prerequisites for source 3.2(ii);
endpoint phases, off-index sums and Cartesian coordinates remain open. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_local_Abelian_primitive_chart (B : HillHminusEnergyRootBox) :
    ∀ n : ℕ+, AnalyticOnNhd ℂ (B.abelianPrimitive n) B.domain ∧
      (∀ q : PeriodOneHminusOne, B.abelianPrimitive n (B.energyCenter,q) = 0) ∧
      (∀ t ∈ B.domain, HasDerivAt (fun E => B.abelianPrimitive n (E,t.2))
        (hillHminusCanonicalEnergyDifferential n t) t.1) ∧
      ∀ E : ℂ, ∀ q : PeriodOneHminusOne, B.abelianPrimitive n (E,q) =
        ∫ᶜ z in Path.segment B.energyCenter E,
          holomorphicOneForm (fun w => hillHminusCanonicalEnergyDifferential n (w,q)) z := by
  intro n
  exact ⟨B.analytic_abelianPrimitive n,B.abelianPrimitive_at_center n,
    (fun t ht => B.hasDerivAt_abelianPrimitive n t.1 t.2 ht),B.abelianPrimitive_eq_curveIntegral n⟩

theorem original_Hill_nonreal_polygonal_Abelian_integrals (k : ℕ) (v : ℕ → ℂ)
    (hpath : ∀ i : Fin k, ∀ E ∈ segment ℝ (v i.val) (v (i.val+1)), E.im ≠ 0) :
    IsOpen (hillHminusAbelianPathDomain k v) ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ hillHminusAbelianPathDomain k v) ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusAbelianPathIntegral n k v) (hillHminusAbelianPathDomain k v) ∧
        ∀ q : OriginalHminusOnePotential,
          hillHminusAbelianPathIntegral n k v (originalPeriodOneCoefficients q) = ∑ i : Fin k,
            ∫ᶜ z in Path.segment (v i.val) (v (i.val+1)),
              holomorphicOneForm (fun E => hillHminusCanonicalPsi n (E,originalPeriodOneCoefficients q)/
                hillHminusContinuedRoot (E,originalPeriodOneCoefficients q)) z := by
  refine ⟨isOpen_hillHminusAbelianPathDomain k v,
    (fun q => real_mem_hillHminusAbelianPathDomain_of_nonreal_segments k v hpath _ (originalPeriodOneCoefficients_real q)),?_⟩
  intro n
  exact ⟨analyticOnNhd_hillHminusAbelianPathIntegral n k v,
    fun q => hillHminusAbelianPathIntegral_eq_physical_of_real n k v _ (originalPeriodOneCoefficients_real q) hpath⟩

theorem original_Hill_Abelian_path_continuation_near_real (k : ℕ) (v : ℕ → ℂ)
    (hpath : ∀ i : Fin k, ∀ E ∈ segment ℝ (v i.val) (v (i.val+1)), E.im ≠ 0)
    (hb : (v k).im ≠ 0) (q : OriginalHminusOnePotential) :
    ∃ B : HillHminusEnergyRootBox, v k ∈ ball B.energyCenter B.energyRadius ∧
      ∃ r : ℝ, 0 < r ∧ ball (originalPeriodOneCoefficients q) r ⊆ B.source ∩ hillHminusAbelianPathDomain k v ∧
        ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusAbelianPathContinuation B n k v)
          (ball B.energyCenter B.energyRadius ×ˢ ball (originalPeriodOneCoefficients q) r) ∧
          ∀ t ∈ ball B.energyCenter B.energyRadius ×ˢ ball (originalPeriodOneCoefficients q) r,
            HasDerivAt (fun E => hillHminusAbelianPathContinuation B n k v (E,t.2))
              (hillHminusCanonicalEnergyDifferential n t) t.1 := by
  have hr := originalPeriodOneCoefficients_real q
  exact exists_common_abelian_path_continuation_chart k v _
    (real_mem_hillHminusAbelianPathDomain_of_nonreal_segments k v hpath _ hr)
    (nonreal_mem_hillHminusCanonicalEnergyRootDomain (v k) hb _ hr)

theorem original_Hill_local_Abelian_transition (B C : HillHminusEnergyRootBox) (n : ℕ+)
    (E : ℂ) (hB : E ∈ ball B.energyCenter B.energyRadius) (hC : E ∈ ball C.energyCenter C.energyRadius) :
    AnalyticOnNhd ℂ (fun q => B.abelianPrimitive n (E,q)-C.abelianPrimitive n (E,q)) (B.source ∩ C.source) ∧
      ∀ q ∈ B.source ∩ C.source, ∀ F : ℂ, (F,q) ∈ B.domain ∩ C.domain →
        B.abelianPrimitive n (F,q)-C.abelianPrimitive n (F,q) =
          B.abelianPrimitive n (E,q)-C.abelianPrimitive n (E,q) :=
  ⟨B.analytic_abelianPrimitive_overlap_transition C n E hB hC,
    fun q hq F hF => B.abelianPrimitive_overlap_difference C n q F E hF ⟨⟨hB,hq.1⟩,hC,hq.2⟩⟩

end NLS.Articles.KdVPseudomeasures
