import NLS.ZakharovShabat.SourceIndexedHigherActionReal
import NLS.ZakharovShabat.SourceGapSampleSummability
import NLS.SequenceSpaces.ShiftedHolderDecay

/-! # Higher-action asymptotics along both integer tails

Every sample from an actual periodic gap is asymptotic to the free spectral
lattice. For real sources, the mean-value samples have an ℓᵖ displacement,
and the original higher action is equivalent to the ordinary action times
the corresponding power of nπ. Closed gaps are included without division
by an action. Lean power k denotes printed level k+1.
-/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- Any selection in the original complex periodic segments is asymptotic to nπ. -/
theorem sourceGapSample_ratio_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (ρ : ℤ → ℂ)
    (hρ : ∀ n, ρ n ∈ sourcePeriodicSegment hp hp1 ψ n) :
    Tendsto (fun n : ℤ => ρ n/((Real.pi:ℂ)*n)) cofinite (𝓝 1) := by
  let a : Coeff p := ⟨fun n => ρ n-(Real.pi:ℂ)*n,
    memℓp_sourcePeriodicSegment_samples hp hp1 ψ ρ hρ⟩
  have ht : Tendsto (fun n : ℤ => ‖a n‖/Real.pi) cofinite (𝓝 0) := by
    simpa using (Coeff.tendsto_norm_apply_cofinite hp a).div_const Real.pi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ht
  filter_upwards [eventually_cofinite_ne (0:ℤ)] with n hn
  have hn1 : (1:ℝ) ≤ ‖(n:ℂ)‖ := by
    rw [Complex.norm_intCast]
    have hi : (1:ℤ) ≤ |n| := by have := abs_pos.mpr hn; omega
    exact_mod_cast hi
  have hden : (Real.pi:ℂ)*n ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast hn)
  rw [div_sub_one hden,norm_div]
  change ‖a n‖/‖(Real.pi:ℂ)*n‖ ≤ ‖a n‖/Real.pi
  apply div_le_div_of_nonneg_left (norm_nonneg _) Real.pi_pos
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos]

/-- Every natural power retains the normalized two-sided limit. -/
theorem sourceGapSample_power_ratio_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (ρ : ℤ → ℂ)
    (hρ : ∀ n, ρ n ∈ sourcePeriodicSegment hp hp1 ψ n) (k : ℕ) :
    Tendsto (fun n : ℤ => (ρ n)^k/((Real.pi:ℂ)*n)^k) cofinite (𝓝 1) := by
  simpa only [div_pow,one_pow] using (sourceGapSample_ratio_tendsto hp hp1 ψ ρ hρ).pow k

/-- The actual mean-value samples simultaneously retain their gap membership,
ℓᵖ displacement, exact action identity, and normalized asymptotic. -/
theorem sourceIndexedHigherAction_exists_asymptotic_samples
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (k : ℕ) :
    ∃ ζ : ℤ → ℝ,
      (∀ n, ζ n ∈ Icc
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re) ∧
      Memℓp (fun n => (ζ n:ℂ)-(Real.pi:ℂ)*n) p ∧
      (∀ n, sourceIndexedHigherAction hp hp1 n k φ.val =
        (ζ n:ℂ)^k*sourceIndexedAction hp hp1 n φ.val) ∧
      Tendsto (fun n : ℤ => (ζ n:ℂ)^k/((Real.pi:ℂ)*n)^k) cofinite (𝓝 1) := by
  choose ζ hζ he using fun n => sourceIndexedHigherAction_eq_power_mul_action hp hp1 φ n k
  have hρ : ∀ n, (ζ n:ℂ) ∈ sourcePeriodicSegment hp hp1 φ.val n :=
    fun n => sourcePeriodicSegment_mem_of_realIcc hp hp1 φ.val φ.property n (ζ n) (hζ n)
  exact ⟨ζ,hζ,memℓp_sourcePeriodicSegment_samples hp hp1 φ.val _ hρ,he,
    sourceGapSample_power_ratio_tendsto hp hp1 φ.val _ hρ k⟩

/-- The asymptotic following (5.6), strengthened to every natural power and
finite p > 1, with the cofinite filter on ℤ expressing |n| → ∞. -/
theorem sourceIndexedHigherAction_asymptotic {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (k : ℕ) :
    Asymptotics.IsEquivalent cofinite (fun n : ℤ => sourceIndexedHigherAction hp hp1 n k φ.val)
      (fun n : ℤ => ((Real.pi:ℂ)*n)^k*sourceIndexedAction hp hp1 n φ.val) := by
  obtain ⟨ζ,_,_,he,ht⟩ := sourceIndexedHigherAction_exists_asymptotic_samples hp hp1 φ k
  have h : Asymptotics.IsEquivalent cofinite (fun n : ℤ => (ζ n:ℂ)^k)
      (fun n : ℤ => ((Real.pi:ℂ)*n)^k) := Asymptotics.isEquivalent_of_tendsto_one ht
  have hmul := h.mul (Asymptotics.IsEquivalent.refl
    (u := fun n : ℤ => sourceIndexedAction hp hp1 n φ.val) (l := cofinite))
  change Asymptotics.IsEquivalent cofinite
    (fun n : ℤ => (ζ n:ℂ)^k*sourceIndexedAction hp hp1 n φ.val)
    (fun n : ℤ => ((Real.pi:ℂ)*n)^k*sourceIndexedAction hp hp1 n φ.val) at hmul
  simpa only [← he] using hmul

end NLS.ZakharovShabat
