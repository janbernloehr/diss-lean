import NLS.KdV.HillNativePositiveAbelianCoordinates
import NLS.Articles.KdVKdV2Frequencies.NativeSummedRegularCorrections

/-! # The actual positive physical Abelian coordinates are natively weighted analytic -/
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

theorem exists_hillPhysical_native_positive_abelian_coordinates :
    ∃ η : ℝ, ∃ Y : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2, ∃ K : ℝ,
      0 < η ∧ 0 < K ∧ AnalyticOnNhd ℂ Y (ball (0 : Coeff 2) η) ∧ Y 0 = 0 ∧
      (∀ u ∈ ball (0 : Coeff 2) η,
        ‖Y u‖ ≤ K*(‖u‖+‖u‖^2) ∧ ∀ j : ℤ, j ≤ 0 → (Y u).val j = 0) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        let q := hillRealWeightedEmbedding SpectralWeight.one p
        let u := SpectralWeight.one.doubleIndex.toCoeff p.val
        ∀ k : ℕ+, (Y u).val (k : ℤ) =
          hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 (k : ℕ) k.property := by
  obtain ⟨εφ,Φ,M,hεφ,_,hΦ,hΦb,hΦphysical⟩ := exists_hillPhysical_native_summed_regular_corrections
  obtain ⟨εy,K,hεy,hεyφ,hK,hYa,hY0,hY⟩ :=
    exists_hillNativePositiveAbelianCoordinates_analytic_bound zero_parity zero_real Φ εφ M hεφ hΦ
      (fun u hu => (hΦb u hu).1)
  obtain ⟨εa,hεa,hAmp⟩ := exists_hillNativeAbelianAmplitudePrefactor_all_physical_matching zero_parity zero_real
  obtain ⟨εp,hεp,_,hPacket⟩ := exists_hillRegularTerminalPhysicalData_all zero_parity zero_real
  let η := min εy (min εa εp)
  have hη : 0 < η := lt_min hεy (lt_min hεa hεp)
  have hsuby : ball (0 : Coeff 2) η ⊆ ball 0 εy := ball_subset_ball (min_le_left _ _)
  have hsubφ : ball (0 : Coeff 2) η ⊆ ball 0 εφ := ball_subset_ball ((min_le_left _ _).trans hεyφ)
  have hηa : η ≤ εa := (min_le_right _ _).trans (min_le_left _ _)
  have hηp : η ≤ εp := (min_le_right _ _).trans (min_le_right _ _)
  let Y := hillNativePositiveAbelianCoordinates zero_parity zero_real Φ
  refine ⟨η,Y,K,hη,hK,hYa.mono hsuby,hY0,?_,?_⟩
  · intro u hu
    exact ⟨(hY u (hsuby hu)).1,(hY u (hsuby hu)).2.2⟩
  · intro p hp
    let q := hillRealWeightedEmbedding SpectralWeight.one p
    let u := SpectralWeight.one.doubleIndex.toCoeff p.val
    change ∀ k : ℕ+, (Y u).val (k : ℤ) =
      hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 (k : ℕ) k.property
    have hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u := by
      dsimp only [q,hillRealWeightedEmbedding,u]
      rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
    have hqsmall : ‖SpectralWeight.one.toCoeff q.val‖ < εp := by
      rw [hcoeff,Coeff.norm_periodDouble]
      exact (mem_ball_zero_iff.mp hp).trans_le hηp
    intro k
    have hA := hAmp q u hcoeff ((mem_ball_zero_iff.mp hp).trans_le hηa) k
    have hphase := hΦphysical p (hsubφ hp) k
    obtain ⟨_,_,_,hτ,_,_,_,hμ,hμB,hU⟩ := hPacket k q hqsmall
    have hT : hillScaledComplexDirichletGapTerminal zero_parity zero_real (1/128) (k : ℕ) (Coeff.periodDouble u) =
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
          (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property)/
        hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 (k : ℕ)
          (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property) := by
      rw [hillScaledComplexDirichletGapTerminal,← hcoeff,hμ,hU _ hμB]
    rw [(hY u (hsuby hp)).2.1 k,hA,hphase,hT,← hcoeff,hμ,hτ]
    exact (hillDirichletAbelianCoordinate_eq_factor q.val q.property.1 q.property.2 (k : ℕ) k.property).symm

end NLS.Articles.KdVKdV2Frequencies
