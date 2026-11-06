import NLS.KdV.HillPhysicalNumeratorGapContainment
import NLS.KdV.HillAbelianImplicitRootReality

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillAbelianPhysicalGapRoot_germ (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → PositiveDeletedCoeff 2 (n:ℤ), AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧
      ∀ᶠ q : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        (∀ k : ℕ, 1 ≤ k → k ≠ n →
          hillAbelianComplexPeriod 0 h0q h0r n k
            ((a (SpectralWeight.one.toCoeff q.val) : Coeff 2),SpectralWeight.one.toCoeff q.val) = 0 ∧
          hillAbelianHilbertRootEnergy (a (SpectralWeight.one.toCoeff q.val) : Coeff 2) k ∈
            segment ℝ (hillRealLabels q.val q.property.1 q.property.2 (2*k-1) : ℂ)
              (hillRealLabels q.val q.property.1 q.property.2 (2*k) : ℂ)) ∧
        hillAbelianComplexPeriod 0 h0q h0r n n
          ((a (SpectralWeight.one.toCoeff q.val) : Coeff 2),SpectralWeight.one.toCoeff q.val) ≠ 0 ∧
        star (a (SpectralWeight.one.toCoeff q.val) : Coeff 2) =
          (a (SpectralWeight.one.toCoeff q.val) : Coeff 2) := by
  obtain ⟨a,ha,ha0,hroots⟩ := exists_hillAbelianComplexPeriod_real_root_germ h0q h0r n hn
  obtain ⟨ε,D,hε,_,hc⟩ := exists_hillComplexPeriodControl h0q h0r
  have hlim : Tendsto (fun p : Coeff 2 => ‖(a p : Coeff 2)‖)
      (𝓝 (0:Coeff 2)) (𝓝 (0:ℝ)) := by
    have hcont : ContinuousAt (fun p : Coeff 2 => ‖(a p : Coeff 2)‖) 0 :=
      (continuous_subtype_val.continuousAt.comp ha.continuousAt).norm
    simpa only [ha0,ZeroMemClass.coe_zero,norm_zero] using hcont.tendsto
  have hsmall : ∀ᶠ p in 𝓝 (0:Coeff 2), ‖(a p : Coeff 2)‖ < Real.pi^2/4 :=
    hlim.eventually (Iio_mem_nhds (by positivity : (0:ℝ) < Real.pi^2/4))
  let P : RealPeriodOneHillPotential → Coeff 2 := fun q => SpectralWeight.one.toCoeff q.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have ht : Tendsto P (𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)) (𝓝 (0:Coeff 2)) := by
    have hP0 : P (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) = 0 := map_zero _
    simpa only [hP0] using hP.tendsto (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
  refine ⟨a,ha,ha0,?_⟩
  filter_upwards [ht.eventually hroots,ht.eventually hsmall,
    ht.eventually (Metric.ball_mem_nhds (0:Coeff 2) hε)] with q hqdata hasmall hpball
  have hp : ‖P q‖ ≤ ε := (show ‖P q‖ < ε by
    simpa only [mem_ball,dist_zero_right] using hpball).le
  have hareal := hqdata.2.2 q.property.2
  refine ⟨?_,hqdata.2.1,hareal⟩
  intro k hk hkn
  exact ⟨hqdata.1 k hk hkn,
    hillAbelianHilbertRootEnergy_mem_physical_gap_of_period_zero h0q h0r ε D hc
      q.val q.property.1 q.property.2 hp n k hn hk hkn (a (P q)) hareal hasmall
        (hqdata.1 k hk hkn)⟩

end NLS.KdV
