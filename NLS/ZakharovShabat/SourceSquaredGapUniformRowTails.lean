import NLS.SequenceSpaces.UniformWeightedRows
import NLS.ZakharovShabat.SourcePeriodicGapTails
import NLS.ZakharovShabat.SourceSquaredGapReciprocalRows

/-!
# Locally uniform decay of squared-gap reciprocal rows

Uniform `ℓᵖ` gap tails make every distant gap coordinate small on one
source neighborhood. Summability of the reciprocal-square kernel then
controls their entire contribution to each row. The finitely many
central gaps are controlled by the kernel's translated-coordinate
decay as the omitted index tends to either infinity.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The physical reciprocal-square rows tend to zero uniformly on a
source neighborhood, including the quasi-Banach range `1<p<2`. -/
theorem exists_uniform_sourceSquaredGapPhysicalRows_lt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs →
        (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) < δ := by
  let b : ℤ → ℝ := fun k => if k = 0 then 0 else |(k:ℝ)|^(-(2:ℝ))
  have hb : Summable b := by
    simpa only [b, zero_add] using
      (NLS.ReciprocalSeries.summable_int_shifted_rpow
        (α := 0) (q := 2) le_rfl (by norm_num))
  have hb0 (k : ℤ) : 0 ≤ b k := by
    by_cases hk : k = 0
    · simp [b, hk]
    · simpa only [b, if_neg hk] using Real.rpow_nonneg (abs_nonneg (k:ℝ)) (-(2:ℝ))
  let T : ℝ := ∑' k : ℤ, b k
  have hT : 0 ≤ T := tsum_nonneg hb0
  let ρ : ℝ := min 1 (δ/(4*(T+1)))
  have hρpos : 0 < ρ := lt_min zero_lt_one (div_pos hδ (by linarith))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρδ : ρ ≤ δ/(4*(T+1)) := min_le_right _ _
  have htailbound : ρ^2*T ≤ δ/4 := by
    have hden : 0 < 4*(T+1) := by linarith
    have hratio : ρ*(4*(T+1)) ≤ δ := (le_div_iff₀ hden).mp hρδ
    have hρsq : ρ^2 ≤ ρ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hρsq hT]
  obtain ⟨M,hM,V,hVopen,hφV,R,hR,hdata⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ hρpos
  let s : Finset ℤ := Finset.Icc (-(M:ℤ)) M
  let A : ℝ := (s.card:ℝ)*R^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let θ : ℝ := δ/(4*(A+1))
  have hθ : 0 < θ := div_pos hδ (by linarith)
  have hcentralbound : A*θ ≤ δ/4 := by
    have hden : 0 < 4*(A+1) := by linarith
    have heq : θ*(4*(A+1)) = δ := by
      exact (div_mul_cancel₀ δ (ne_of_gt hden)).trans rfl
    nlinarith [mul_nonneg hA hθ.le]
  let a : V → ℤ → ℝ := fun x m => ‖sourcePeriodicGapDisplacement hp hp1 x.1 m‖^2
  have ha0 (x : V) (m : ℤ) : 0 ≤ a x m := by dsimp [a]; positivity
  have haR (x : V) (m : ℤ) : a x m ≤ R^2 := by
    have hcoord := lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans hp1))
      (sourcePeriodicGapDisplacement hp hp1 x.1) m
    have hbound := (hdata x.1 x.2).1
    dsimp [a]
    exact (pow_le_pow_left₀ (norm_nonneg _) (hcoord.trans hbound) 2)
  have haρ (x : V) (m : ℤ) (hm : m ∉ s) : a x m ≤ ρ^2 := by
    let g := sourcePeriodicGapDisplacement hp hp1 x.1
    have htail := (hdata x.1 x.2).2 M le_rfl
    have hcoord := lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans hp1))
      (g-Coeff.truncate s g) m
    have hpoint : ‖g m‖ ≤ ‖g-Coeff.truncate s g‖ := by
      simpa only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply,
        if_neg hm, sub_zero] using hcoord
    dsimp [a]
    exact pow_le_pow_left₀ (norm_nonneg _) (hpoint.trans htail) 2
  obtain ⟨K,hK⟩ := exists_uniform_weighted_row_bound b hb hb0 s
    (R^2) (ρ^2) θ (sq_nonneg _) (sq_nonneg _) hθ a ha0 haR haρ
  refine ⟨V,hVopen,hφV,K,?_⟩
  intro ψ hψ n hn
  have hrow := hK ⟨ψ,hψ⟩ n hn
  have hterm (m : ℤ) :
      sourceSquaredGapReciprocalTerm hp hp1 ψ n m =
        a ⟨ψ,hψ⟩ m * b (m-n) := by
    by_cases hm : m = n
    · subst m
      simp [sourceSquaredGapReciprocalTerm, b]
    · simp only [sourceSquaredGapReciprocalTerm, if_neg hm, a, b,
        if_neg (sub_ne_zero.mpr hm)]
  have hrow' : (∑' m : ℤ,
      sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤
      ρ^2*T + A*θ := by
    rw [tsum_congr hterm]
    simpa only [A, T] using hrow
  have hsum : ρ^2*T + A*θ ≤ δ/2 := by linarith
  exact lt_of_le_of_lt (hrow'.trans hsum) (by linarith)

/-- One index threshold works for the half-unit row condition for all
sources in a common open neighborhood. -/
theorem exists_uniform_sourceSquaredGapPhysicalRows_half_unit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs →
        (C^2/4) *
          (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤ 1/2 := by
  have hCpos : 0 < C := by linarith
  have hC2 : 0 < C^2 := sq_pos_of_pos hCpos
  obtain ⟨V,hVopen,hφV,K,hK⟩ :=
    exists_uniform_sourceSquaredGapPhysicalRows_lt hp hp1 φ
      (show 0 < 2/C^2 by positivity)
  refine ⟨V,hVopen,hφV,K,?_⟩
  intro ψ hψ n hn
  have hlt := hK ψ hψ n hn
  have hmul := (lt_div_iff₀ hC2).mp hlt
  nlinarith

end NLS.ZakharovShabat
