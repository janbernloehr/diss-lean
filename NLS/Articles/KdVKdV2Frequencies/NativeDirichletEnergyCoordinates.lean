import NLS.KdV.HillNativeDirichletEnergyCoordinates
import NLS.KdV.HillAllRegularTerminalData

/-! # Actual physical Dirichlet energy deviations in a native Hilbert space

One complex period-one L2 ball precedes all physical sources and positive
gaps. The mean is subtracted exactly; the derivative is the cosine Fourier
projection and the nonlinear remainder has a full quadratic Hilbert bound.
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

theorem exists_hillPhysical_native_dirichlet_energy_coordinates :
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
          (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property : ℂ)-freeHillEnergy k-u 0 := by
  obtain ⟨ηd,K,hηd,hK,hDa,hD0,hDD,hD⟩ :=
    exists_hillNativeDirichletEnergyDeviations_analytic_bound zero_parity zero_real
  obtain ⟨εp,hεp,_,hphysical⟩ := exists_hillRegularTerminalPhysicalData_all zero_parity zero_real
  let η := min ηd εp
  have hη : 0 < η := lt_min hηd hεp
  have hsub : ball (0 : Coeff 2) η ⊆ ball (0 : Coeff 2) ηd := ball_subset_ball (min_le_left _ _)
  let D := hillNativeDirichletEnergyDeviations zero_parity zero_real
  refine ⟨η,D,K,hη,hK,hDa.mono hsub,hD0,hDD,?_,?_⟩
  · intro u hu
    exact ⟨(hD u (hsub hu)).1,(hD u (hsub hu)).2.1,(hD u (hsub hu)).2.2.2⟩
  · intro p hp
    let q := hillRealWeightedEmbedding SpectralWeight.one p
    let u := SpectralWeight.one.doubleIndex.toCoeff p.val
    change ∀ k : ℕ+, D u (k : ℤ) =
      (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property : ℂ)-freeHillEnergy k-u 0
    intro k
    have hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u := by
      dsimp only [q,hillRealWeightedEmbedding,u]
      rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
    have hqsmall : ‖SpectralWeight.one.toCoeff q.val‖ < εp := by
      rw [hcoeff,Coeff.norm_periodDouble]
      exact (mem_ball_zero_iff.mp hp).trans_le (min_le_right _ _)
    obtain ⟨_,_,_,_,_,_,_,hμ,_,_⟩ := hphysical k q hqsmall
    rw [(hD u (hsub hp)).2.2.1 k,← hcoeff,hμ]

end NLS.Articles.KdVKdV2Frequencies
