import NLS.Articles.KdVKdV2Frequencies.AllRegularGapSolutions
import NLS.KdV.HillAllNativeRegularTerminal
import NLS.KdV.HillAllRegularTerminalData
import NLS.KdV.HillRegularTerminalPhysicalComparison
import NLS.SequenceSpaces.PositiveDeletedProjectionBounds

/-! # All actual physical regular corrections on one native Hilbert ball

The finite terminal head and the uniform tail are identified together,
before all gap and output indices. This is a uniformly bounded native
analytic family; gap-index decay and the infinite phase sum are not asserted.
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

theorem exists_hillPhysical_native_all_regular_corrections :
    ∃ η : ℝ, ∃ β : ℕ+ → Coeff 2 → Coeff 2, ∃ M : ℝ,
      0 < η ∧ 0 < M ∧
      (∀ k : ℕ+, AnalyticOnNhd ℂ (β k) (ball (0 : Coeff 2) η) ∧
        ∀ u ∈ ball (0 : Coeff 2) η, ‖β k u‖ ≤ M ∧ ∀ j : ℤ, j ≤ 0 → β k u j = 0) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        let q := hillRealWeightedEmbedding SpectralWeight.one p
        let u := SpectralWeight.one.doubleIndex.toCoeff p.val
        ∀ k n : ℕ+, β k u (n : ℤ) =
          hillRegularAbelianCorrection q.val q.property.1 q.property.2 (n : ℕ) n.property (k : ℕ) k.property := by
  obtain ⟨ρ,G,H,C,hρ,hC,_,hgap,hphysical⟩ := exists_hillPhysical_native_all_regular_gap_solutions
  obtain ⟨εt,hεt,hterminal⟩ := exists_hillNative_all_regular_terminal_analytic_bound zero_parity zero_real
  obtain ⟨εp,hεp,_,hdata⟩ := exists_hillRegularTerminalPhysicalData_all zero_parity zero_real
  let η := min ρ (min εt εp)
  have hη : 0 < η := lt_min hρ (lt_min hεt hεp)
  have hsub : ball (0 : Coeff 2) η ⊆ ball (0 : Coeff 2) ρ := ball_subset_ball (min_le_left _ _)
  have hηt : η ≤ εt := (min_le_right _ _).trans (min_le_left _ _)
  have hηp : η ≤ εp := (min_le_right _ _).trans (min_le_right _ _)
  let β := fun k : ℕ+ => Coeff.positiveDeletedProjection 2 0 ∘
    hillNativeRegularTerminal zero_parity zero_real (H k) k
  refine ⟨η,β,9*Real.pi*C/4,hη,by positivity,?_,?_⟩
  · intro k
    have ht := hterminal η hηt k (H k) (18*Real.pi*C) (by positivity)
      ((hgap k).2.2.1.mono (prod_mono Subset.rfl hsub))
      (fun u hu => (hgap k).2.2.2.2 u (hsub hu))
    refine ⟨fun u hu => ((Coeff.positiveDeletedProjection 2 0).analyticAt _).comp (ht.1 u hu),?_⟩
    intro u hu
    refine ⟨(Coeff.norm_positiveDeletedProjection_le 0 _).trans ((ht.2 u hu).trans_eq (by ring)),?_⟩
    intro j hj
    exact (Coeff.positiveDeletedProjection_apply 2 0 j _).trans (if_neg (by omega))
  · intro p hp
    let q := hillRealWeightedEmbedding SpectralWeight.one p
    let u := SpectralWeight.one.doubleIndex.toCoeff p.val
    change ∀ k n : ℕ+, β k u (n : ℤ) =
      hillRegularAbelianCorrection q.val q.property.1 q.property.2 (n : ℕ) n.property (k : ℕ) k.property
    intro k n
    have hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u := by
      dsimp only [q,hillRealWeightedEmbedding,u]
      rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
    have hqsmall : ‖SpectralWeight.one.toCoeff q.val‖ < εp := by
      rw [hcoeff,Coeff.norm_periodDouble]
      exact (mem_ball_zero_iff.mp hp).trans_le hηp
    change Coeff.positiveDeletedProjection 2 0 (hillNativeRegularTerminal zero_parity zero_real (H k) k u) (n : ℤ) = _
    rw [Coeff.positiveDeletedProjection_apply,if_pos (show (0:ℤ) < n ∧ (n:ℤ) ≠ 0 by
      have hn : (0:ℤ) < n := by exact_mod_cast n.pos
      exact ⟨hn,ne_of_gt hn⟩)]
    apply hillNativeRegularTerminal_eq_of_physical_data zero_parity zero_real k q u hcoeff (hdata k q hqsmall) (H k) G
    · intro E hE
      exact ((hgap k).2.2.1 (E,u) ⟨hE,hsub hp⟩).comp
        (f := fun E : ℂ => (E,u)) (analyticAt_id.prod analyticAt_const)
    · exact (hgap k).2.2.2.1 u (hsub hp)
    · exact hphysical p (hsub hp)

end NLS.Articles.KdVKdV2Frequencies
