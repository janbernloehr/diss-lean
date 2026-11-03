import NLS.KdV.HillAbelianPhysicalRootSequence
import NLS.KdV.HillIntrinsicNormalizedGapPeriodGerm

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillAbelianCandidatePeriod_physicalRootSequence_eq
    (ε D : ℝ) (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (n k : ℕ) (hk : 1 ≤ k)
    (a : Coeff 2) (ha : star a = a) :
    hillAbelianCandidatePeriod q hq hr (hillAbelianPhysicalRootSequence q hq hr n a) n k =
      hillAbelianComplexPeriod 0 h0q h0r n k (a,SpectralWeight.one.toCoeff q) := by
  have he : hillAbelianPsiCandidate (hillAbelianPhysicalRootSequence q hq hr n a) n =
      (fun E => hillAbelianHilbertPsi n (E,a)) := by
    funext E
    exact hillAbelianPsiCandidate_physicalRootSequence_eq q hq hr n a ha E
  unfold hillAbelianCandidatePeriod
  rw [he]
  exact (hillAbelianComplexPeriod_eq_intrinsic_physical h0q h0r ε D hc q hq hr hp n k hk a).symm

theorem hillAbelianNormalizedComplexPsi_eq_gapbox_candidate
    (ε D : ℝ) (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (n : ℕ) (hn : 1 ≤ n)
    (a : Coeff 2) (ha : star a = a) (E : ℂ) :
    hillAbelianNormalizedComplexPsi h0q h0r n (a,SpectralWeight.one.toCoeff q) E =
      hillAbelianPsiCandidate (hillAbelianPhysicalRootSequence q hq hr n a) n E/
        hillAbelianCandidatePeriod q hq hr (hillAbelianPhysicalRootSequence q hq hr n a) n n := by
  rw [hillAbelianPsiCandidate_physicalRootSequence_eq q hq hr n a ha E,
    hillAbelianCandidatePeriod_physicalRootSequence_eq h0q h0r ε D hc q hq hr hp n n hn a ha]
  rfl

theorem exists_hillAbelian_gapbox_normalized_germ (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → PositiveDeletedCoeff 2 (n:ℤ), AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧
      ∀ᶠ q : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        let roots := hillAbelianPhysicalRootSequence q.val q.property.1 q.property.2 n
          (a (SpectralWeight.one.toCoeff q.val) : Coeff 2)
        roots ∈ hillGapRootBox q.val q.property.1 q.property.2 ∧
        hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots n n ≠ 0 ∧
        ∀ k : ℕ, 1 ≤ k →
          hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots n k/
            hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots n n =
              if k = n then 1 else 0 := by
  obtain ⟨a,ha,ha0,hroots⟩ := exists_hillAbelianPhysicalGapRoot_germ h0q h0r n hn
  obtain ⟨ε,D,hε,_,hc⟩ := exists_hillComplexPeriodControl h0q h0r
  let P : RealPeriodOneHillPotential → Coeff 2 := fun q => SpectralWeight.one.toCoeff q.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have ht : Tendsto P (𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)) (𝓝 (0:Coeff 2)) := by
    have hP0 : P (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) = 0 := map_zero _
    simpa only [hP0] using hP.tendsto (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
  refine ⟨a,ha,ha0,?_⟩
  filter_upwards [hroots,ht.eventually (Metric.ball_mem_nhds (0:Coeff 2) hε)] with q hqdata hpball
  dsimp only []
  have hp : ‖P q‖ ≤ ε := (show ‖P q‖ < ε by
    simpa only [mem_ball,dist_zero_right] using hpball).le
  have hareal := hqdata.2.2
  have hperiod (k : ℕ) (hk : 1 ≤ k) := hillAbelianCandidatePeriod_physicalRootSequence_eq
    h0q h0r ε D hc q.val q.property.1 q.property.2 hp n k hk (a (P q)) hareal
  have hnonzero : hillAbelianCandidatePeriod q.val q.property.1 q.property.2
      (hillAbelianPhysicalRootSequence q.val q.property.1 q.property.2 n (a (P q))) n n ≠ 0 := by
    rw [hperiod n hn]
    exact hqdata.2.1
  refine ⟨hillAbelianPhysicalRootSequence_mem_gapRootBox q.val q.property.1 q.property.2 n (a (P q))
    (fun k hk hkn => (hqdata.1 k hk hkn).2),hnonzero,?_⟩
  intro k hk
  by_cases hkn : k = n
  · subst k
    rw [if_pos rfl,div_self hnonzero]
  · rw [if_neg hkn,hperiod k hk,(hqdata.1 k hk hkn).1,zero_div]

end NLS.KdV
