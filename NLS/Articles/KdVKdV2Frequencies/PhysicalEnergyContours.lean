import NLS.Articles.KdVKdV2Frequencies.PhysicalNormalizedDensity
import NLS.KdV.HillNativeEnergyDensityTransfer
import NLS.KdV.HillHminusOneEnergyPeriodTransfer
import NLS.KdV.HillRadiusEnergyCirclePhysicalRoot
/-! # Actual native physical families on free energy contours

One complex L2 source ball precedes every positive energy contour and
output index. Full Hilbert numerator and density bounds, genuine Bochner
Kronecker periods and actual canonical physical root matching are retained.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by
  rw [map_zero]
  exact Submodule.zero_mem _

private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
  rw [map_zero]
  intro k
  simp

/-- The actual normalized physical numerator family has full Hilbert C/k
energy-disc and boundary-density bounds and native Kronecker energy periods
on a common complex source ball. Every real boundary root is canonical. -/
theorem exists_hillPhysical_native_energy_contours :
    ∃ η : ℝ, ∃ G : ℂ × Coeff 2 → Coeff 2,
      0 < η ∧ AnalyticOnNhd ℂ G (univ ×ˢ ball (0 : Coeff 2) η) ∧
      (∀ n : ℕ+, ∀ E : ℂ, G (E,0) (n : ℤ) = classicalHillFreePsi n E) ∧
      (∀ t ∈ univ ×ˢ ball (0 : Coeff 2) η, ∀ m : ℤ, m ≤ 0 → G t m = 0) ∧
      (∀ u ∈ ball (0 : Coeff 2) η, ∀ k : ℕ+,
        CircleIntegrable (fun z : ℂ => ((2*z)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)) • G (z^2,u))
          ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) ∧
        (2*(Real.pi : ℂ))⁻¹ • (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
          ((2*z)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)) • G (z^2,u)) = lp.single 2 (k : ℤ) 1) ∧
      (∃ K : ℝ, 0 < K ∧ ∀ u ∈ ball (0 : Coeff 2) η, ∀ k : ℕ+,
        (∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ), ‖G (E,u)‖ ≤ K/(k : ℝ)) ∧
        (∀ E ∈ sphere (freeHillEnergy k) (k : ℝ),
          (E,periodOneL2Inclusion u) ∈ hillHminusContinuationDomain ∧
          ‖(hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u)‖ ≤ K/(k : ℝ)) ∧
        CircleIntegrable (fun E : ℂ => (hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u))
          (freeHillEnergy k) (k : ℝ) ∧
        (2*(Real.pi : ℂ))⁻¹ • (∮ E in C(freeHillEnergy k,(k : ℝ)),
          (hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u)) = lp.single 2 (k : ℤ) 1) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        let q := hillRealWeightedEmbedding SpectralWeight.one p
        let u := SpectralWeight.one.doubleIndex.toCoeff p.val
        (∀ k : ℕ+, ∀ E ∈ sphere (freeHillEnergy k) (k : ℝ),
          E ∈ hillL2RealCutDomain q.val q.property.1 q.property.2 ∧
          hillHminusContinuedRoot (E,periodOneL2Inclusion u) =
            hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E) ∧
        ∀ n : ℕ+, ∀ E : ℂ, G (E,u) (n : ℤ) =
          hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 (n : ℕ) n.property E := by
  obtain ⟨ρ,G,hρ,hGa,hfree,hzero,hperiod,⟨K,hK,hfreq⟩,hphysical⟩ :=
    exists_hillPhysical_normalized_numerators_uniform_density
  obtain ⟨θ,hθ,hθρ,C,hC,henergy⟩ := exists_uniform_energy_density_bound_of_frequency_family ρ hρ G hGa K hK hfreq
  obtain ⟨δ,hδ,htransfer⟩ := exists_hillHminus_frequency_energy_period_transfer
  obtain ⟨η,hη,hs⟩ := exists_common_ball_linear_preimage periodOneL2Inclusion δ (θ/2)
    hδ (by positivity) univ isOpen_univ (mem_univ _)
  have hηθ : ball (0 : Coeff 2) η ⊆ ball (0 : Coeff 2) θ := by
    intro u hu
    rw [mem_ball_zero_iff]
    exact ((hs u hu).2.2).trans_lt (by linarith)
  have hηρ := hηθ.trans hθρ
  refine ⟨η,G,hη,hGa.mono (prod_mono Subset.rfl hηρ),hfree,?_,?_,⟨C,hC,?_⟩,?_⟩
  · intro t ht m hm
    exact hzero t ⟨ht.1,hηρ ht.2⟩ m hm
  · intro u hu k
    exact hperiod u (hηρ hu) k
  · intro u hu k
    have hb := henergy u (hηθ hu) k
    have ht := htransfer (periodOneL2Inclusion u) (hs u hu).1 k
    have hGe : AnalyticOnNhd ℂ (fun E => G (E,u)) univ := by
      intro E _
      exact (hGa (E,u) ⟨mem_univ _,hηρ hu⟩).comp
        (f := fun z : ℂ => (z,u)) (analyticAt_id.prod analyticAt_const)
    exact ⟨hb.1,hb.2,hillHminus_native_frequency_period_gives_energy_period
      (periodOneL2Inclusion u) k (fun E => G (E,u)) hGe ht.1 ht.2 (hperiod u (hηρ hu) k)⟩
  · intro p hp
    let q := hillRealWeightedEmbedding SpectralWeight.one p
    let u := SpectralWeight.one.doubleIndex.toCoeff p.val
    have hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u := by
      dsimp only [q,hillRealWeightedEmbedding,u]
      rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
    refine ⟨?_,hphysical p (hηρ hp)⟩
    intro k E hE
    exact hillRadiusEnergyCircle_actual_physical_root zero_parity zero_real q.val
      q.property.1 q.property.2 u hcoeff k E hE ((henergy u (hηθ hp) k).2 E hE).1
end NLS.Articles.KdVKdV2Frequencies
