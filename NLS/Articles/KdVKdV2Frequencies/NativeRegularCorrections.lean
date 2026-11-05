import NLS.SequenceSpaces.PositiveDeletedProjectionBounds
import NLS.Articles.KdVKdV2Frequencies.NativeRegularGapSolutions
import NLS.KdV.HillNativeTerminalPhysical

/-! # Actual physical regular corrections in one native Hilbert neighborhood

Moving Dirichlet evaluation of the actual filled-gap quadratic solutions
produces one complex analytic Hilbert family before all high gaps and output
indices. At every real source its positive coordinates equal the physical
regular corrections, including the own mode and collapsed gaps.
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

/-- One common native complex L2 neighborhood realizes all positive
physical output coordinates of every high regular correction. The uniform
full norm bound asserted here does not assert summability over the gaps. -/
theorem exists_hillPhysical_native_regular_corrections :
    ∃ η : ℝ, ∃ β : ℕ+ → Coeff 2 → Coeff 2, ∃ N : ℕ, ∃ M : ℝ,
      0 < η ∧ 1 ≤ N ∧ 0 < M ∧
      (∀ k : ℕ+, N ≤ (k : ℕ) → AnalyticOnNhd ℂ (β k) (ball (0 : Coeff 2) η) ∧
        ∀ u ∈ ball (0 : Coeff 2) η, ‖β k u‖ ≤ M ∧
          ∀ j : ℤ, j ≤ 0 → β k u j = 0) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        let q := hillRealWeightedEmbedding SpectralWeight.one p
        let u := SpectralWeight.one.doubleIndex.toCoeff p.val
        ∀ k : ℕ+, N ≤ (k : ℕ) → ∀ n : ℕ+,
          β k u (n : ℤ) = hillRegularAbelianCorrection q.val q.property.1 q.property.2
            (n : ℕ) n.property (k : ℕ) k.property := by
  obtain ⟨ρ,G,H,Ng,C,hρ,hNg,hC,_,hH,hphysical⟩ :=
    exists_hillPhysical_native_regular_gap_solutions
  let η := min ρ (1/2)
  have hη : 0 < η := lt_min hρ (by norm_num)
  have hsub : ball (0 : Coeff 2) η ⊆ ball (0 : Coeff 2) ρ := ball_subset_ball (min_le_left _ _)
  have hsource (u : Coeff 2) (hu : u ∈ ball 0 η) : Coeff.periodDouble u ∈ ball (0 : Coeff 2) 1 := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (mem_ball_zero_iff.mp hu).trans_le ((min_le_right ρ (1/2)).trans (by norm_num))
  obtain ⟨Nt,_,hterminal⟩ := exists_hillNative_regular_terminal_analytic_bound zero_parity zero_real η 1 hsource
  obtain ⟨Np,_,hmatch⟩ := exists_hillNative_regular_terminal_physical_matching zero_parity zero_real 1
  let β := fun k : ℕ+ => Coeff.positiveDeletedProjection 2 0 ∘
    hillNativeRegularTerminal zero_parity zero_real (H k) k
  let N := max Ng (max Nt Np)
  refine ⟨η,β,N,9*Real.pi*C/4,hη,hNg.trans (le_max_left _ _),by positivity,?_,?_⟩
  · intro k hk
    have hkg : Ng ≤ (k : ℕ) := (le_max_left Ng (max Nt Np)).trans hk
    have hkt : Nt ≤ (k : ℕ) := (le_max_left Nt Np).trans ((le_max_right Ng (max Nt Np)).trans hk)
    have ht := hterminal k hkt (H k) (18*Real.pi*C) (by positivity)
      ((hH k hkg).1.mono (prod_mono Subset.rfl hsub))
      (fun u hu => (hH k hkg).2.2 u (hsub hu))
    refine ⟨fun u hu => ((Coeff.positiveDeletedProjection 2 0).analyticAt _).comp (ht.1 u hu),?_⟩
    intro u hu
    refine ⟨(Coeff.norm_positiveDeletedProjection_le 0 _).trans ((ht.2 u hu).trans_eq (by ring)),?_⟩
    intro j hj
    exact (Coeff.positiveDeletedProjection_apply 2 0 j _).trans (if_neg (by omega))
  · intro p hp
    let q := hillRealWeightedEmbedding SpectralWeight.one p
    let u := SpectralWeight.one.doubleIndex.toCoeff p.val
    change ∀ k : ℕ+, N ≤ (k : ℕ) → ∀ n : ℕ+, β k u (n : ℤ) =
      hillRegularAbelianCorrection q.val q.property.1 q.property.2 (n : ℕ) n.property (k : ℕ) k.property
    intro k hk n
    have hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u := by
      dsimp only [q,hillRealWeightedEmbedding,u]
      rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
    have hsmall : ‖SpectralWeight.one.toCoeff q.val‖ ≤ 1 := by
      rw [hcoeff]
      exact (mem_ball_zero_iff.mp (hsource u hp)).le
    have hkg : Ng ≤ (k : ℕ) := (le_max_left Ng (max Nt Np)).trans hk
    have hkp : Np ≤ (k : ℕ) := (le_max_right Nt Np).trans ((le_max_right Ng (max Nt Np)).trans hk)
    change Coeff.positiveDeletedProjection 2 0 (hillNativeRegularTerminal zero_parity zero_real (H k) k u) (n : ℤ) = _
    rw [Coeff.positiveDeletedProjection_apply,if_pos (show (0:ℤ) < n ∧ (n:ℤ) ≠ 0 by
      have hn : (0:ℤ) < n := by exact_mod_cast n.pos
      exact ⟨hn,ne_of_gt hn⟩)]
    apply hmatch q.val q.property.1 q.property.2 hsmall u hcoeff k hkp (H k)
      (fun E => hillNativeRegularGapNumerator zero_parity zero_real G k (E,u))
    · intro E hE
      exact ((hH k hkg).1 (E,u) ⟨hE,hsub hp⟩).comp
        (f := fun E : ℂ => (E,u)) (analyticAt_id.prod analyticAt_const)
    · exact (hH k hkg).2.1 u (hsub hp)
    · intro m E hE
      exact (hphysical p (hsub hp)).2 k hkg m E
        (closedBall_subset_closedBall (by linarith [show (0 : ℝ) < k by positivity] :
          3*(k : ℝ)/4 ≤ k) (ball_subset_closedBall hE))

end NLS.Articles.KdVKdV2Frequencies
