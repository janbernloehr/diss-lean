import NLS.KdV.HillDirichletAnalyticLabels
import NLS.KdV.HillLocalDirichletChart
import NLS.KdV.HillDeflatedLocalPhysicalMatching
import NLS.KdV.HillOpenGapHalfLength
import NLS.KdV.HillRadiusQuadraticData
import NLS.KdV.HillFilledFreeGapRoot

/-! # Output-independent physical terminal data near each free gap

A small real source neighborhood fixes the physical symmetric gap data,
Dirichlet label and actual deflated-root sheet on a fixed energy ball.
The ball may depend on the gap, but never on an output coordinate.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def HillRegularTerminalPhysicalData (k : ℕ+) (q : RealPeriodOneHillPotential) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ (k : ℝ) ∧
    hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (SpectralWeight.one.toCoeff q.val) = (hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ) ∧
    hillLocalGapSquare 0 h0q h0r (k : ℕ) (SpectralWeight.one.toCoeff q.val) = (2*(hillRealGapHalfLength q.val q.property.1 q.property.2 (k : ℕ) : ℂ))^2 ∧
    ‖(hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ)-freeHillEnergy k‖ ≤ r/16 ∧
    ‖(hillRealGapHalfLength q.val q.property.1 q.property.2 (k : ℕ) : ℂ)‖ ≤ r/16 ∧
    hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (SpectralWeight.one.toCoeff q.val) = (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property : ℂ) ∧
    (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property : ℂ) ∈ ball (freeHillEnergy k) r ∧
    ∀ E ∈ ball (freeHillEnergy k) r,
      hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,SpectralWeight.one.toCoeff q.val) =
        hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 (k : ℕ) E

theorem eventually_hillRegularTerminalPhysicalData (k : ℕ+) :
    ∀ᶠ q : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      HillRegularTerminalPhysicalData h0q h0r k q := by
  let q0 : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  let c := freeHillEnergy k
  let R := hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)
  have hc := (hillFreeGap_energy_radius_geometry h0q h0r k).1
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).1
    (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).2.1
  obtain ⟨r0,hr0,W,hW,h0W,hroot⟩ := exists_hillLocalDeflatedComplexRoot_local_physical_matching
    0 h0q h0r (k : ℕ) k.property c (by rw [hc];exact mem_ball_self hR)
  let r := min (k : ℝ) (r0/2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrk : r ≤ (k : ℝ) := min_le_left _ _
  have hrr0 : r ≤ r0 := (min_le_right _ _).trans (by linarith)
  obtain ⟨S,hS,h0S,hsymmetric⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood 0 h0q h0r (k : ℕ) k.property
  obtain ⟨V,hV,h0V,_,hmu⟩ := exists_hillScaledDirichletRoot_local_analytic_chart h0q h0r (k : ℕ) k.property (1/128) (by norm_num) (by norm_num)
  have hcoef : Continuous (fun q : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff q.val) :=
    SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hsource : ∀ᶠ q in 𝓝 q0, SpectralWeight.one.toCoeff q.val ∈ V :=
    hcoef.continuousAt (by simpa only [q0,map_zero] using hV.mem_nhds h0V)
  have hτcont := (Complex.continuous_ofReal.comp (continuous_hillRealGapCenter (k : ℕ))).continuousAt (x := q0)
  have hδcont := (Complex.continuous_ofReal.comp (continuous_hillRealGapHalfLength (k : ℕ))).continuousAt (x := q0)
  have hμcont := (Complex.continuous_ofReal.comp (continuous_hillDirichletEnergy (k : ℕ) k.property)).continuousAt (x := q0)
  change ContinuousAt (fun q : RealPeriodOneHillPotential => (hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ)) q0 at hτcont
  change ContinuousAt (fun q : RealPeriodOneHillPotential => (hillRealGapHalfLength q.val q.property.1 q.property.2 (k : ℕ) : ℂ)) q0 at hδcont
  change ContinuousAt (fun q : RealPeriodOneHillPotential => (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property : ℂ)) q0 at hμcont
  have hτ0 : (hillRealGapCenter q0.val q0.property.1 q0.property.2 (k : ℕ) : ℂ) = c := hc
  have hδ0 : (hillRealGapHalfLength q0.val q0.property.1 q0.property.2 (k : ℕ) : ℂ) = 0 := by
    rw [hillFreeGapHalfLength h0q h0r (k : ℕ) k.property,ofReal_zero]
  have hμ0 : (hillDirichletEnergy q0.val q0.property.1 q0.property.2 (k : ℕ) k.property : ℂ) = c := by
    rw [hillDirichletEnergy_zero_potential h0q h0r (k : ℕ) k.property]
    exact (congrArg Complex.ofReal (hillFreeGapCenter h0q h0r (k : ℕ) k.property)).symm.trans hc
  have hτnear : ∀ᶠ q in 𝓝 q0, (hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ) ∈ ball c (r/16) :=
    hτcont (by
      change ball c (r/16) ∈ 𝓝 (hillRealGapCenter q0.val q0.property.1 q0.property.2 (k : ℕ) : ℂ)
      rw [hτ0]
      exact ball_mem_nhds _ (by positivity))
  have hδnear : ∀ᶠ q in 𝓝 q0, (hillRealGapHalfLength q.val q.property.1 q.property.2 (k : ℕ) : ℂ) ∈ ball 0 (r/16) :=
    hδcont (by
      change ball 0 (r/16) ∈ 𝓝 (hillRealGapHalfLength q0.val q0.property.1 q0.property.2 (k : ℕ) : ℂ)
      rw [hδ0]
      exact ball_mem_nhds _ (by positivity))
  have hμnear : ∀ᶠ q in 𝓝 q0, (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property : ℂ) ∈
      ball c (min ((1/128)*R) r) :=
    hμcont (by
      change ball c (min ((1/128)*R) r) ∈ 𝓝 (hillDirichletEnergy q0.val q0.property.1 q0.property.2 (k : ℕ) k.property : ℂ)
      rw [hμ0]
      exact ball_mem_nhds _ (lt_min (by positivity) hr))
  filter_upwards [hW.mem_nhds h0W,hS.mem_nhds h0S,hsource,hτnear,hδnear,hμnear] with q hqW hqS hqV hτ hδ hμ
  have hμK : (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property : ℂ) ∈
      closedBall (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ) ((1/128)*R) := by
    rw [hc]
    exact ball_subset_closedBall (ball_subset_ball (min_le_left _ _) hμ)
  have hm := ((hmu _ hqV).2.2.2 _ hμK).mp (hillDirichletEnergy_zero q.val q.property.1 q.property.2 (k : ℕ) k.property)
  refine ⟨r,hr,hrk,(hsymmetric q hqS).1,(hsymmetric q hqS).2,
    (mem_ball_iff_norm.mp hτ).le,?_,hm.symm,ball_subset_ball (min_le_right _ _) hμ,?_⟩
  · exact (mem_ball_zero_iff.mp hδ).le
  · intro E hE
    have hdata := hroot q hqW E (ball_subset_ball hrr0 hE)
    exact (hillFilledFreeGapRoot_eq_local h0q h0r (k : ℕ) _ E hdata.1.1.2.1).trans hdata.2.2

end NLS.KdV
