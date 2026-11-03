import NLS.KdV.HillGlobalDifferentialLocalIdentification

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillAbelianSelectedGlobalPsi_free_root_germ (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ), AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧
      ∀ᶠ q : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        hillAbelianNormalizedComplexPsi h0q h0r n
          ((a (SpectralWeight.one.toCoeff q.val) : Coeff 2),SpectralWeight.one.toCoeff q.val) =
            hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn := by
  obtain ⟨a,ha,ha0,hroots⟩ := exists_hillAbelianPhysicalGapRoot_germ h0q h0r n hn
  obtain ⟨ε,D,hε,_,hc⟩ := exists_hillComplexPeriodControl h0q h0r
  let P : RealPeriodOneHillPotential → Coeff 2 := fun q => SpectralWeight.one.toCoeff q.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have ht : Tendsto P (𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)) (𝓝 (0 : Coeff 2)) := by
    have he : P (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) = 0 := map_zero _
    simpa only [he] using hP.tendsto (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
  refine ⟨a,ha,ha0,?_⟩
  filter_upwards [hroots,ht.eventually (Metric.ball_mem_nhds (0 : Coeff 2) hε)] with q hqdata hpball
  have hp : ‖P q‖ ≤ ε := (show ‖P q‖ < ε by simpa only [mem_ball,dist_zero_right] using hpball).le
  exact hillAbelianNormalizedComplexPsi_eq_selected_of_physical_roots q.val q.property.1 q.property.2
    h0q h0r ε D hc hp n hn (a (P q)) hqdata.2.2
    (fun k hk hkn => (hqdata.1 k hk hkn).2) (fun k hk hkn => (hqdata.1 k hk hkn).1)

theorem exists_hillAbelianSelectedGlobalPsi_joint_analytic_free_extension (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : ℂ × Coeff 2 → ℂ, (∀ E : ℂ, AnalyticAt ℂ G (E,0)) ∧
      ∀ᶠ q : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        ∀ E : ℂ, G (E,SpectralWeight.one.toCoeff q.val) =
          hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E := by
  obtain ⟨a,ha,ha0,hmatch⟩ := exists_hillAbelianSelectedGlobalPsi_free_root_germ h0q h0r n hn
  let L : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  have hac : AnalyticAt ℂ (fun p : Coeff 2 => (a p : Coeff 2)) 0 := (L.analyticAt (a 0)).comp ha
  have hac0 : (a 0 : Coeff 2) = 0 := by rw [ha0];rfl
  refine ⟨fun t => hillAbelianNormalizedComplexPsi h0q h0r n ((a t.2 : Coeff 2),t.2) t.1,?_,?_⟩
  · intro E
    exact analyticAt_hillAbelianNormalizedComplexPsi_root_germ h0q h0r n hn
      (fun p => (a p : Coeff 2)) hac hac0 E
  · filter_upwards [hmatch] with q hq
    exact congrFun hq

end NLS.KdV
