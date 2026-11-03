import NLS.KdV.HillAbelianRootBox

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillAbelianNumeratorProduct (σ : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∏' k : ℕ, hillAbelianNumeratorFactor σ n k z

theorem exists_hillAbelianNumeratorFactor_uniform_majorant (n : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ σ ∈ hillGapRootBox q hq hr,
      ∀ k : ℕ, N ≤ k → ∀ z : ℂ, ‖z‖ ≤ R →
        ‖hillAbelianNumeratorFactor σ n k z-1‖ ≤ u k := by
  obtain ⟨N,u,hu,hbound⟩ := exists_hillGapRootEnergyFactor_uniform_majorant q hq hr R hR
  refine ⟨N,u,hu,?_⟩
  intro σ hσ k hk z hz
  unfold hillAbelianNumeratorFactor
  split_ifs
  · simp only [sub_self,norm_zero]
    exact (norm_nonneg _).trans (hbound σ hσ k hk z hz)
  · exact hbound σ hσ k hk z hz

theorem summable_norm_hillAbelianNumeratorFactor_sub_one
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n : ℕ) (z : ℂ) :
    Summable (fun k : ℕ => ‖hillAbelianNumeratorFactor σ n k z-1‖) := by
  obtain ⟨N,u,hu,hbound⟩ :=
    exists_hillAbelianNumeratorFactor_uniform_majorant q hq hr n ‖z‖ (norm_nonneg z)
  apply hu.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N] with k hk
  simpa only [norm_norm] using hbound σ hσ k hk z le_rfl

theorem multipliable_hillAbelianNumeratorFactors
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n : ℕ) (z : ℂ) :
    Multipliable (fun k : ℕ => hillAbelianNumeratorFactor σ n k z) := by
  have h := multipliable_one_add_of_summable
    (summable_norm_hillAbelianNumeratorFactor_sub_one q hq hr σ hσ n z)
  convert! h using 1
  funext k
  ring

theorem hasProdUniformlyOn_hillAbelianNumeratorFactors
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n : ℕ)
    (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun k z => hillAbelianNumeratorFactor σ n k z)
      (hillAbelianNumeratorProduct σ n) K := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨N,u,hu,hmajor⟩ :=
    exists_hillAbelianNumeratorFactor_uniform_majorant q hq hr n R hR.le
  have hevent : ∀ᶠ k : ℕ in cofinite, ∀ z ∈ K,
      ‖hillAbelianNumeratorFactor σ n k z-1‖ ≤ u k := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with k hk
    exact fun z hz => hmajor σ hσ k hk z (hbound z hz)
  have hc (k : ℕ) : ContinuousOn (fun z => hillAbelianNumeratorFactor σ n k z-1) K := by
    unfold hillAbelianNumeratorFactor hillGapRootEnergyFactor
    split_ifs <;> fun_prop
  have hp := hu.hasProdUniformlyOn_one_add hK hevent hc
  have he (k : ℕ) (z : ℂ) : 1+(hillAbelianNumeratorFactor σ n k z-1) =
      hillAbelianNumeratorFactor σ n k z := by ring
  simp only [he] at hp
  convert! hp using 1

theorem hasProdLocallyUniformlyOn_hillAbelianNumeratorFactors
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n : ℕ) :
    HasProdLocallyUniformlyOn (fun k z => hillAbelianNumeratorFactor σ n k z)
      (hillAbelianNumeratorProduct σ n) univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  exact fun K _ hK => hasProdUniformlyOn_hillAbelianNumeratorFactors q hq hr σ hσ n K hK

theorem analyticOnNhd_hillAbelianNumeratorProduct
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n : ℕ) :
    AnalyticOnNhd ℂ (hillAbelianNumeratorProduct σ n) univ := by
  have hf (k : ℕ) : DifferentiableOn ℂ (hillAbelianNumeratorFactor σ n k) univ := by
    unfold hillAbelianNumeratorFactor hillGapRootEnergyFactor
    split_ifs <;> fun_prop
  have hd : DifferentiableOn ℂ (hillAbelianNumeratorProduct σ n) univ :=
    (hasProdLocallyUniformlyOn_hillAbelianNumeratorFactors q hq hr σ hσ n).differentiableOn
      (Eventually.of_forall (fun s => DifferentiableOn.fun_finsetProd (fun k _ => hf k)))
      isOpen_univ
  exact hd.analyticOnNhd isOpen_univ

end NLS.KdV
