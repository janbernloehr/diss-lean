import NLS.ZakharovShabat.SourceStandardRootCentralBounded
import NLS.ZakharovShabat.SourceStandardRootMixedBounds

/-!
# Equation (2.10) on one all-index isolating-disc family

Uniform tail isolation, a bounded central radius, and the mixed-pair
geometry yield a connected source neighborhood on which every nearby
spectral cluster lies in a pairwise-disjoint assigned disc. One constant
bounds each standard root by the signed-index separation, for every
distinct source and root index.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem widen_root_index_bounds
    (a c d r : ℝ) (ha : 0 < a) (hac : a ≤ c) (hd : 0 ≤ d)
    (hlo : a⁻¹*d ≤ r) (hhi : r ≤ a*d) :
    c⁻¹*d ≤ r ∧ r ≤ c*d := by
  have hinv : c⁻¹ ≤ a⁻¹ := inv_anti₀ ha hac
  exact ⟨(mul_le_mul_of_nonneg_right hinv hd).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right hac hd)⟩

/-- One connected local source neighborhood and one family of isolating
discs carry equation (2.10) for every pair of distinct signed indices. -/
theorem exists_local_source_all_index_root_bounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ c : ℝ, 1 ≤ c ∧
        ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
          (∀ ψ ∈ V, ∀ n : ℤ, sourceSpectralCluster hp hp1 ψ n ⊆
            sourceIsolatingDisc hp hp1 φ N ε n) ∧
          (∀ i j : ℤ, i ≠ j →
            Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
              (sourceIsolatingDisc hp hp1 φ N ε j)) ∧
          ∀ ψ ∈ V, ∀ m n : ℤ, m ≠ n →
            ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε m,
              c⁻¹*|((m-n : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ ∧
              ‖sourceStandardRoot hp hp1 ψ n z‖ ≤
                c*|((m-n : ℤ) : ℝ)| := by
  obtain ⟨N₀, Ut, hUto, hφt, htail⟩ :=
    exists_uniform_source_tail_isolation hp hp1 φ
  let N := N₀ + 1
  have hN₀ : N₀ < N := by dsimp [N]; omega
  have hpos : N₀ < (N : ℤ).natAbs := by simpa using hN₀
  have hneg : N₀ < (-(N : ℤ)).natAbs := by simpa using hN₀
  have houterR := (htail φ hφt (N : ℤ) hpos).2.1
  have houterL := (htail φ hφt (-(N : ℤ)) hneg).1
  obtain ⟨δ, hδ, hδmax, cC, hcC, Vc, hVco, _hVcc, hφVc, hcentralRoot⟩ :=
    exists_local_source_central_root_index_bounds_bounded hp hp1 φ hφ N
      (Real.pi/4) (by positivity)
  obtain ⟨ε, hε, hεδ, Uc, hUco, hφUc, hcentral, hcentralDisjoint⟩ :=
    exists_local_sourceClusterDiscs_finite_block_bounded hp hp1 φ hφ
      (Finset.Icc (-(N : ℤ)) (N : ℤ)) hδ
  have hεmax : ε ≤ Real.pi/4 := hεδ.trans hδmax
  obtain ⟨cM, hcM, hmixed⟩ :=
    exists_source_central_tail_root_bounds hp hp1 φ hφ N ε
      hε.le hεmax houterL houterR
  let c : ℝ := max cC (max cM (3*Real.pi/2))
  have hCc : cC ≤ c := le_max_left _ _
  have hMc : cM ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hTc : 3*Real.pi/2 ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  have hc : 1 ≤ c := hcC.trans hCc
  have hcinv : c⁻¹ ≤ (1:ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hc
  have htailInv : c⁻¹ ≤ Real.pi/2 := by linarith [Real.pi_gt_three]
  let U : Set (CoeffPair p) := (Vc ∩ Uc) ∩ Ut
  have hUopen : IsOpen U := (hVco.inter hUco).inter hUto
  have hφU : φ ∈ U := ⟨⟨hφVc, hφUc⟩, hφt⟩
  have hcluster : ∀ ψ ∈ U, ∀ n : ℤ,
      sourceSpectralCluster hp hp1 ψ n ⊆
        sourceIsolatingDisc hp hp1 φ N ε n := by
    intro ψ hψ n
    by_cases hn : n.natAbs ≤ N
    · simp only [sourceIsolatingDisc, if_pos hn]
      have hmem : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      exact hcentral ψ hψ.1.2 n hmem
    · simp only [sourceIsolatingDisc, if_neg hn]
      have hnt : N₀ < n.natAbs := by omega
      intro z hz
      obtain ⟨hL, hR, hD, hN, hC⟩ := htail ψ hψ.2 n hnt
      rcases hz with h | h | h | h | h
      · rw [h]; exact hL
      · rw [h]; exact hR
      · rw [h]; exact hD
      · rw [h]; exact hN
      · rw [h]; exact hC
  have hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j) := by
    intro i j hij
    by_cases hi : i.natAbs ≤ N
    · by_cases hj : j.natAbs ≤ N
      · have hiIcc : i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
          simp only [Finset.mem_Icc]
          omega
        have hjIcc : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
          simp only [Finset.mem_Icc]
          omega
        simp only [sourceIsolatingDisc, if_pos hi, if_pos hj]
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact hcentralDisjoint i hiIcc j hjIcc hlt
        · exact (hcentralDisjoint j hjIcc i hiIcc hgt).symm
      · simpa only [sourceIsolatingDisc, if_pos hi, if_neg hj] using
          (source_central_tail_pointwise_geometry hp hp1 φ hφ N ε
            hε.le hεmax houterL houterR i j hi (by omega)).1
    · by_cases hj : j.natAbs ≤ N
      · simpa only [sourceIsolatingDisc, if_neg hi, if_pos hj] using
          (source_central_tail_pointwise_geometry hp hp1 φ hφ N ε
            hε.le hεmax houterL houterR j i hj (by omega)).1.symm
      · simpa only [sourceIsolatingDisc, if_neg hi, if_neg hj] using
          refinedResonantDisk_disjoint hij
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hφU)
  refine ⟨N, ε, hε, hεmax, c, hc, ball φ r, Metric.isOpen_ball,
    isConnected_ball hr, mem_ball_self hr, ?_, hdisjoint, ?_⟩
  · intro ψ hψ n
    exact hcluster ψ (hrU hψ) n
  · intro ψ hψ m n hmn z hz
    have hψU : ψ ∈ U := hrU hψ
    have hd : 0 ≤ |((m-n : ℤ) : ℝ)| := abs_nonneg _
    by_cases hm : m.natAbs ≤ N
    · by_cases hn : n.natAbs ≤ N
      · have hzC : z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) m := by
          simpa only [sourceIsolatingDisc, if_pos hm] using hz
        have hzD := sourceClusterDisc_mono_constant_margin hp hp1 φ
          ε δ hεδ m hzC
        exact widen_root_index_bounds cC c _ _ (by linarith) hCc hd
          (hcentralRoot ψ hψU.1.1 m n hm hn hmn z hzD).1
          (hcentralRoot ψ hψU.1.1 m n hm hn hmn z hzD).2
      · have hzC : z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) m := by
          simpa only [sourceIsolatingDisc, if_pos hm] using hz
        have hmix := (hmixed ψ (hcluster ψ hψU) m n hm (by omega)).1 z hzC
        exact widen_root_index_bounds cM c _ _ (by linarith) hMc hd
          hmix.1 hmix.2
    · by_cases hn : n.natAbs ≤ N
      · have hzT : z ∈ refinedResonantDisk m := by
          simpa only [sourceIsolatingDisc, if_neg hm] using hz
        have hmix := (hmixed ψ (hcluster ψ hψU) n m hn (by omega)).2 z hzT
        have hdiff : |((n-m : ℤ) : ℝ)| = |((m-n : ℤ) : ℝ)| := by
          rw [show n-m = -(m-n) by omega, Int.cast_neg, abs_neg]
        rw [hdiff] at hmix
        exact widen_root_index_bounds cM c _ _ (by linarith) hMc hd
          hmix.1 hmix.2
      · obtain ⟨htl, htu⟩ := sourceStandardRoot_tail_disc_norm_bounds
          hp hp1 φ ψ N ε hmn hm hn (hcluster ψ hψU n) hz
        exact ⟨(mul_le_mul_of_nonneg_right htailInv hd).trans htl,
          htu.trans (mul_le_mul_of_nonneg_right hTc hd)⟩

end NLS.ZakharovShabat
