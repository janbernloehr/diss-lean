import NLS.KdV.HillAbelianNumeratorProduct

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem continuous_hillAbelianNumeratorFactor_joint (n k : ℕ) :
    Continuous (fun p : (hillGapRootBox q hq hr) × ℂ =>
      hillAbelianNumeratorFactor p.1.val n k p.2) := by
  unfold hillAbelianNumeratorFactor hillGapRootEnergyFactor
  split_ifs
  · exact continuous_const
  · exact ((continuous_ofReal.comp ((continuous_apply k).comp
      (continuous_subtype_val.comp continuous_fst))).sub continuous_snd).div_const _

theorem hasProdUniformlyOn_hillAbelianNumeratorFactors_joint (n : ℕ)
    (K : Set ((hillGapRootBox q hq hr) × ℂ)) (hK : IsCompact K) :
    HasProdUniformlyOn
      (fun k (p : (hillGapRootBox q hq hr) × ℂ) =>
        hillAbelianNumeratorFactor p.1.val n k p.2)
      (fun p => hillAbelianNumeratorProduct p.1.val n p.2) K := by
  obtain ⟨R,hR,hbound⟩ := (hK.image continuous_snd).isBounded.exists_pos_norm_le
  obtain ⟨N,u,hu,hmajor⟩ :=
    exists_hillAbelianNumeratorFactor_uniform_majorant q hq hr n R hR.le
  have hevent : ∀ᶠ k : ℕ in cofinite, ∀ p ∈ K,
      ‖hillAbelianNumeratorFactor p.1.val n k p.2-1‖ ≤ u k := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with k hk
    exact fun p hp => hmajor p.1.val p.1.property k hk p.2
      (hbound p.2 (mem_image_of_mem Prod.snd hp))
  have hc (k : ℕ) : ContinuousOn
      (fun p : (hillGapRootBox q hq hr) × ℂ =>
        hillAbelianNumeratorFactor p.1.val n k p.2-1) K := by
    exact ((continuous_hillAbelianNumeratorFactor_joint q hq hr n k).sub
      continuous_const).continuousOn
  have hp := hu.hasProdUniformlyOn_one_add hK hevent hc
  have he (k : ℕ) (p : (hillGapRootBox q hq hr) × ℂ) :
      1+(hillAbelianNumeratorFactor p.1.val n k p.2-1) =
        hillAbelianNumeratorFactor p.1.val n k p.2 := by ring
  simp only [he] at hp
  convert! hp using 1

theorem continuous_hillAbelianNumeratorProduct_joint (n : ℕ) :
    Continuous (fun p : (hillGapRootBox q hq hr) × ℂ =>
      hillAbelianNumeratorProduct p.1.val n p.2) := by
  let : CompactSpace (hillGapRootBox q hq hr) :=
    isCompact_iff_compactSpace.mp (isCompact_hillGapRootBox q hq hr)
  have hp : HasProdLocallyUniformlyOn
      (fun k (p : (hillGapRootBox q hq hr) × ℂ) =>
        hillAbelianNumeratorFactor p.1.val n k p.2)
      (fun p => hillAbelianNumeratorProduct p.1.val n p.2) univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    exact fun K _ hK => hasProdUniformlyOn_hillAbelianNumeratorFactors_joint q hq hr n K hK
  apply continuousOn_univ.mp
  apply hp.continuousOn
  apply Filter.Eventually.frequently
  apply Eventually.of_forall
  intro S
  apply Continuous.continuousOn
  apply continuous_finsetProd
  intro k _
  exact continuous_hillAbelianNumeratorFactor_joint q hq hr n k

def hillAbelianPsiCandidate (σ : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  2/((n : ℂ)*Real.pi)*hillAbelianNumeratorProduct σ n z

theorem analyticOnNhd_hillAbelianPsiCandidate
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n : ℕ) :
    AnalyticOnNhd ℂ (hillAbelianPsiCandidate σ n) univ :=
  analyticOnNhd_const.mul (analyticOnNhd_hillAbelianNumeratorProduct q hq hr σ hσ n)

theorem continuous_hillAbelianPsiCandidate_joint (n : ℕ) :
    Continuous (fun p : (hillGapRootBox q hq hr) × ℂ =>
      hillAbelianPsiCandidate p.1.val n p.2) :=
  continuous_const.mul (continuous_hillAbelianNumeratorProduct_joint q hq hr n)

end NLS.KdV
