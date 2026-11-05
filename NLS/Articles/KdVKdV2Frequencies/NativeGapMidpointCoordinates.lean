import NLS.KdV.HillNativeDirichletMidpointCoordinates
import NLS.KdV.HillAllRegularTerminalData

/-! # Actual symmetric gap midpoints and Dirichlet displacements in Hilbert norm

One complex period-one L2 ball precedes all physical sources and positive
gaps, including first and closed gaps and potentials with nonzero mean.
-/
noncomputable section
open Set Metric Complex
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by
  rw [map_zero]
  exact Submodule.zero_mem _
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
  rw [map_zero]
  intro k
  simp

theorem exists_hillPhysical_native_gap_midpoint_remainder :
    ∃ η : ℝ, ∃ R : Coeff 2 → Coeff 2, ∃ K : ℝ,
      0 < η ∧ 0 < K ∧ AnalyticOnNhd ℂ R (ball (0 : Coeff 2) η) ∧ R 0 = 0 ∧
      HasFDerivAt R (0 : Coeff 2 →L[ℂ] Coeff 2) 0 ∧
      (∀ u ∈ ball (0 : Coeff 2) η,
        ‖R u‖ ≤ K*‖u‖^2 ∧ ∀ j : ℤ, j ≤ 0 → R u j = 0) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        let q := hillRealWeightedEmbedding SpectralWeight.one p
        let u := SpectralWeight.one.doubleIndex.toCoeff p.val
        ∀ k : ℕ+, R u (k : ℤ) =
          (hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ)-freeHillEnergy k-u 0 := by
  obtain ⟨ηr,K,hηr,hK,hRa,hR0,hDR,hR⟩ :=
    exists_hillNativeGapMidpointRemainder_analytic_bound zero_parity zero_real
  obtain ⟨εp,hεp,_,hphysical⟩ := exists_hillRegularTerminalPhysicalData_all zero_parity zero_real
  let η := min ηr εp
  have hη : 0 < η := lt_min hηr hεp
  have hsub : ball (0 : Coeff 2) η ⊆ ball (0 : Coeff 2) ηr := ball_subset_ball (min_le_left _ _)
  let R := hillNativeGapMidpointRemainder zero_parity zero_real
  refine ⟨η,R,K,hη,hK,hRa.mono hsub,hR0,hDR,?_,?_⟩
  · intro u hu
    exact ⟨(hR u (hsub hu)).1,(hR u (hsub hu)).2.2⟩
  · intro p hp
    let q := hillRealWeightedEmbedding SpectralWeight.one p
    let u := SpectralWeight.one.doubleIndex.toCoeff p.val
    change ∀ k : ℕ+, R u (k : ℤ) =
      (hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ)-freeHillEnergy k-u 0
    intro k
    have hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u := by
      dsimp only [q,hillRealWeightedEmbedding,u]
      rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
    have hqsmall : ‖SpectralWeight.one.toCoeff q.val‖ < εp := by
      rw [hcoeff,Coeff.norm_periodDouble]
      exact (mem_ball_zero_iff.mp hp).trans_le (min_le_right _ _)
    obtain ⟨_,_,_,hτ,_,_,_,_,_,_⟩ := hphysical k q hqsmall
    rw [(hR u (hsub hp)).2.1 k,← hcoeff,hτ]

theorem exists_hillPhysical_native_dirichlet_midpoint_coordinates :
    ∃ η : ℝ, ∃ D : Coeff 2 → Coeff 2, ∃ K : ℝ,
      0 < η ∧ 0 < K ∧ AnalyticOnNhd ℂ D (ball (0 : Coeff 2) η) ∧ D 0 = 0 ∧
      HasFDerivAt D hillDirichletEnergyLinearPart 0 ∧
      (∀ u ∈ ball (0 : Coeff 2) η,
        ‖D u‖ ≤ ‖u‖+K*‖u‖^2 ∧ ‖D u-hillDirichletEnergyLinearPart u‖ ≤ K*‖u‖^2 ∧
          ∀ j : ℤ, j ≤ 0 → D u j = 0) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        let q := hillRealWeightedEmbedding SpectralWeight.one p
        let u := SpectralWeight.one.doubleIndex.toCoeff p.val
        ∀ k : ℕ+, D u (k : ℤ) =
          (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property : ℂ)-
            (hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ) := by
  obtain ⟨ηd,K,hηd,hK,hDa,hD0,hDD,hD⟩ :=
    exists_hillNativeDirichletMidpointDisplacements_analytic_bound zero_parity zero_real
  obtain ⟨εp,hεp,_,hphysical⟩ := exists_hillRegularTerminalPhysicalData_all zero_parity zero_real
  let η := min ηd εp
  have hη : 0 < η := lt_min hηd hεp
  have hsub : ball (0 : Coeff 2) η ⊆ ball (0 : Coeff 2) ηd := ball_subset_ball (min_le_left _ _)
  let D := hillNativeDirichletMidpointDisplacements zero_parity zero_real
  refine ⟨η,D,K,hη,hK,hDa.mono hsub,hD0,hDD,?_,?_⟩
  · intro u hu
    exact ⟨(hD u (hsub hu)).1,(hD u (hsub hu)).2.1,(hD u (hsub hu)).2.2.2⟩
  · intro p hp
    let q := hillRealWeightedEmbedding SpectralWeight.one p
    let u := SpectralWeight.one.doubleIndex.toCoeff p.val
    change ∀ k : ℕ+, D u (k : ℤ) =
      (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property : ℂ)-
            (hillRealGapCenter q.val q.property.1 q.property.2 (k : ℕ) : ℂ)
    intro k
    have hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u := by
      dsimp only [q,hillRealWeightedEmbedding,u]
      rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
    have hqsmall : ‖SpectralWeight.one.toCoeff q.val‖ < εp := by
      rw [hcoeff,Coeff.norm_periodDouble]
      exact (mem_ball_zero_iff.mp hp).trans_le (min_le_right _ _)
    obtain ⟨_,_,_,hτ,_,_,_,hμ,_,_⟩ := hphysical k q hqsmall
    rw [(hD u (hsub hp)).2.2.1 k,← hcoeff,hμ,hτ]


end NLS.Articles.KdVKdV2Frequencies
