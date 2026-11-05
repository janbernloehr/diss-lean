import NLS.Articles.KdVKdV2Frequencies.AllRegularCorrections
import NLS.KdV.HillNativeDirichletTerminalSequence

/-! # Actual physical regular corrections with genuine complex Hilbert control

One native terminal ell2 sequence controls the full output norm of every
regular correction by its kth coefficient divided by k, on one source ball.
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

theorem exists_hillPhysical_native_regular_correction_hilbert_control :
    ∃ η : ℝ, ∃ β : ℕ+ → Coeff 2 → Coeff 2, ∃ a : Coeff 2 → Coeff 2, ∃ A B : ℝ,
      0 < η ∧ 0 < A ∧ 0 < B ∧
      AnalyticOnNhd ℂ a (ball (0 : Coeff 2) η) ∧
      (∀ u ∈ ball (0 : Coeff 2) η, ‖a u‖ ≤ B) ∧
      (∀ k : ℕ+, AnalyticOnNhd ℂ (β k) (ball (0 : Coeff 2) η) ∧
        ∀ u ∈ ball (0 : Coeff 2) η,
          ‖β k u‖ ≤ A*‖a u (k : ℤ)‖/(k : ℝ) ∧ ∀ j : ℤ, j ≤ 0 → β k u j = 0) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        let q := hillRealWeightedEmbedding SpectralWeight.one p
        let u := SpectralWeight.one.doubleIndex.toCoeff p.val
        ∀ k n : ℕ+, β k u (n : ℤ) =
          hillRegularAbelianCorrection q.val q.property.1 q.property.2 (n : ℕ) n.property (k : ℕ) k.property := by
  obtain ⟨ρ,G,H,C,hρ,hC,_,hgap,hphysical⟩ := exists_hillPhysical_native_all_regular_gap_solutions
  obtain ⟨εt,hεt,hterminal⟩ := exists_hillNative_all_regular_terminal_analytic_bound zero_parity zero_real
  obtain ⟨εp,hεp,_,hdata⟩ := exists_hillRegularTerminalPhysicalData_all zero_parity zero_real
  obtain ⟨εx,K,hεx,hK,hXa,hX⟩ := exists_hillNativeDirichletGapTerminals_analytic_bound zero_parity zero_real
  obtain ⟨εm,hεm,_,hmu⟩ := exists_hillDirichlet_all_terminal_data zero_parity zero_real
  let σ := min ρ (min εt εp)
  let τ := min εx (min εm 1)
  let η := min σ τ
  have hη : 0 < η := lt_min (lt_min hρ (lt_min hεt hεp)) (lt_min hεx (lt_min hεm zero_lt_one))
  have hηρ : η ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have hηt : η ≤ εt := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηp : η ≤ εp := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hηx : η ≤ εx := (min_le_right _ _).trans (min_le_left _ _)
  have hηm : η ≤ εm := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη1 : η ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsub : ball (0 : Coeff 2) η ⊆ ball (0 : Coeff 2) ρ := ball_subset_ball hηρ
  let a := hillNativeDirichletGapTerminals zero_parity zero_real
  let β := fun k : ℕ+ => Coeff.positiveDeletedProjection 2 0 ∘
    hillNativeRegularTerminal zero_parity zero_real (H k) k
  refine ⟨η,β,a,18*Real.pi*C,2*K,hη,by positivity,by positivity,hXa.mono (ball_subset_ball hηx),?_,?_,?_⟩
  · intro u hu
    have hnu : ‖u‖ ≤ 1 := (mem_ball_zero_iff.mp hu).le.trans hη1
    apply (hX u (ball_subset_ball hηx hu)).1.trans
    calc
      _ ≤ K*2 := mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg u]) hK.le
      _ = _ := by ring
  · intro k
    have ht := hterminal η hηt k (H k) (18*Real.pi*C) (by positivity)
      ((hgap k).2.2.1.mono (prod_mono Subset.rfl hsub))
      (fun u hu => (hgap k).2.2.2.2 u (hsub hu))
    refine ⟨fun u hu => ((Coeff.positiveDeletedProjection 2 0).analyticAt _).comp (ht.1 u hu),?_⟩
    intro u hu
    refine ⟨?_,?_⟩
    · let μ := hillScaledDirichletRoot zero_parity zero_real (1/128) (k : ℕ) (Coeff.periodDouble u)
      have hup : Coeff.periodDouble u ∈ ball (0 : Coeff 2) εm := by
        rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
        exact (mem_ball_zero_iff.mp hu).trans_le hηm
      have hμ : μ ∈ closedBall (freeHillEnergy k) ((k : ℝ)/4) := by
        rw [mem_closedBall_iff_norm]
        have h := ((hmu k).2.2 _ hup).1
        linarith [show (0 : ℝ) < k by positivity]
      have hb := (hgap k).2.2.2.2 u (hsub hu) μ hμ
      have hx := (hX u (ball_subset_ball hηx hu)).2.1 k
      apply (Coeff.norm_positiveDeletedProjection_le 0 _).trans
      change ‖hillNativeRegularTerminal zero_parity zero_real (H k) k u‖ ≤ _
      rw [hillNativeRegularTerminal,norm_smul,norm_mul,norm_I,one_mul,← hx]
      exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)
    · intro j hj
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
