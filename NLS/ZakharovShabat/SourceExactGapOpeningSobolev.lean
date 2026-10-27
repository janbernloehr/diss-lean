import NLS.ZakharovShabat.SourceExactGapOpening
import NLS.ZakharovShabat.SourceFiniteGapCurveSobolev

/-! # Exact numerical gap-opening approximants in every Sobolev norm

These approximants realize the literal assertion in the proof of Lemma 20.2:
all unselected gap lengths are fixed, and convergence holds in H1.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The exact numerical gap-opening curve is continuous in every native
nonnegative Sobolev norm through the original finite-gap source. -/
theorem exists_finiteGap_exact_sobolev_opening
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n = 0)
    (σ : ℝ) (hσ : 0 ≤ σ) :
    ∃ a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ),
      ∃ G : ℝ → weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ),
        originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a = φ ∧
        Continuous G ∧ G 0 = a ∧ ∀ t : ℝ,
          let ψ := originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (G t)
          ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num) ∧ ∀ k : ℤ,
            canonicalPeriodicGap (by simp) (by norm_num)
              (periodOnePotential ψ.val) (periodOnePotential_mem _) k =
              if k = n then ((|t| : ℝ) : ℂ) else canonicalPeriodicGap (by simp) (by norm_num)
                (periodOnePotential φ.val) (periodOnePotential_mem _) k := by
  classical
  obtain ⟨γ,hγ,hγ0,hgap⟩ := D.exists_finiteGap_exact_gap_opening φ hf n hn
  let S := insert n hf.toFinset
  have hS (t : ℝ) (k : ℤ) (hk : k ∉ S) :
      canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (γ t).val) (periodOnePotential_mem _) k = 0 := by
    have hkn : k ≠ n := fun h => hk (h ▸ Finset.mem_insert_self n hf.toFinset)
    rw [(hgap t).2 k,if_neg hkn]
    by_contra hne
    exact hk (Finset.mem_insert.mpr (Or.inr (hf.mem_toFinset.mpr hne)))
  obtain ⟨G,hG,hinc⟩ := D.exists_continuous_sobolev_lift_of_finite_gap_support γ hγ S hS σ hσ
  refine ⟨G 0,G,(hinc 0).trans hγ0,hG,rfl,fun t => ?_⟩
  change originalWeightedRealSource _ (G t) ∈ _ ∧ _
  rw [hinc t]
  exact hgap t

/-- The explicit amplitudes 1/(l+1) give finite-gap approximants converging
in the chosen Sobolev norm. Every unselected numerical gap length is fixed,
and the selected collapsed gap is open at every approximant. -/
theorem exists_finiteGap_exact_sobolev_approximants
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n = 0)
    (σ : ℝ) (hσ : 0 ≤ σ) :
    ∃ a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ),
      ∃ G : ℕ → weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ),
        originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a = φ ∧
        Tendsto G atTop (𝓝 a) ∧ ∀ l : ℕ,
          let ψ := originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (G l)
          ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num) ∧
          canonicalPeriodicGap (by simp) (by norm_num)
            (periodOnePotential ψ.val) (periodOnePotential_mem _) n ≠ 0 ∧
          ∀ k : ℤ, k ≠ n → canonicalPeriodicGap (by simp) (by norm_num)
            (periodOnePotential ψ.val) (periodOnePotential_mem _) k =
            canonicalPeriodicGap (by simp) (by norm_num)
              (periodOnePotential φ.val) (periodOnePotential_mem _) k := by
  obtain ⟨a,F,ha,hF,hF0,hgap⟩ := D.exists_finiteGap_exact_sobolev_opening φ hf n hn σ hσ
  have hlim : Tendsto F (𝓝 0) (𝓝 a) := hF0 ▸ hF.continuousAt.tendsto (x := 0)
  refine ⟨a,fun l => F (1/((l : ℝ)+1)),ha,
    hlim.comp tendsto_one_div_add_atTop_nhds_zero_nat,fun l => ?_⟩
  refine ⟨(hgap (1/((l : ℝ)+1))).1,?_,fun k hk => ?_⟩
  · rw [(hgap (1/((l : ℝ)+1))).2 n,if_pos rfl]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (abs_pos.mpr (by positivity)))
  · rw [(hgap (1/((l : ℝ)+1))).2 k,if_neg hk]

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
