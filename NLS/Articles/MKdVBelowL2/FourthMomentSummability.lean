import NLS.ZakharovShabat.SourceAbelianMomentLemma20_3
import NLS.SequenceSpaces.RefinedTripleProduct
import NLS.ZakharovShabat.SourceAbelianMomentSquaredGapAtlas
import NLS.ZakharovShabat.SourceAbelianMomentExponent

/-! # Absolute convergence of the H₄ weighted second-moment sum

The article's candidate is -12 ∑ k, k Ω⁽²⁾ₙₖ. This file proves absolute
convergence on a constructed neighborhood for 1 < p ≤ 3, including the
Hilbert case. It does not identify this candidate with the physical H₄
Hamiltonian derivative or assert the full p>3 estimates of Theorem 1.3.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞}

/-- Cubing a gap sequence is summable up to exponent three, with sharp norm control. -/
theorem exists_summable_cube (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3)
    (g : Coeff p) :
    ∃ b : Coeff 1, (∀ k, b k = g k ^ 3) ∧ ‖b‖ ≤ ‖g‖ ^ 3 := by
  have hthird : ENNReal.ofReal (p.toReal / 3) ≤ 1 := by
    rw [Coeff.thirdExponent_eq_div hp]
    exact (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by simpa using hp3)
  obtain ⟨b,hb,hn⟩ := Coeff.exists_refined_triple_product hp
    (zero_lt_one.trans hp1) (by simp : (1 : ℝ≥0∞) ≠ ⊤) zero_lt_one hthird g g g
  exact ⟨b,fun k => by rw [hb k]; ring,by simpa [pow_succ] using hn⟩

/-- Multiplication by k costs at most |n|+1 in the off-diagonal reciprocal kernel. -/
theorem norm_index_ratio_le (n k : ℤ) (hk : k ≠ n) :
    ‖(k : ℂ) / ((n - k : ℤ) : ℂ)‖ ≤ |(n : ℝ)| + 1 := by
  have hne : n - k ≠ 0 := sub_ne_zero.mpr hk.symm
  have hone : (1 : ℝ) ≤ |((n - k : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hne
  have htri : |(k : ℝ)| ≤ |(n : ℝ)| + |((n - k : ℤ) : ℝ)| := by
    have h := abs_sub_le (n : ℝ) 0 ((n - k : ℤ) : ℝ)
    push_cast at h ⊢
    simpa [abs_sub_comm] using h
  rw [norm_div, Complex.norm_intCast, Complex.norm_intCast]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hone)).mpr
  nlinarith [abs_nonneg (n : ℝ)]

variable [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- An actual refined moment row and its cubic gap imply the weighted sum is absolute. -/
theorem summable_weighted_moment_of_row
    (A : SourceAbelianMomentAtlas hp hp1 W s) (hp3 : p ≤ 3)
    (ψ : CoeffPair p) (n : ℤ) (a : Coeff p)
    (hrow : ∀ k : ℤ, k ≠ n → A.moment n k 2 ψ =
      (sourcePeriodicGapDisplacement hp hp1 ψ k)^3 / ((n-k : ℤ) : ℂ) * a k) :
    Summable (fun k : ℤ => ‖(k : ℂ) * A.moment n k 2 ψ‖) := by
  obtain ⟨b,hb,_⟩ := exists_summable_cube hp hp1 hp3
    (sourcePeriodicGapDisplacement hp hp1 ψ)
  have hs : Summable (fun k => (|(n : ℝ)| + 1) * ‖a‖ * ‖b k‖) :=
    b.property.norm.summable_of_one.mul_left _
  have hbound (k : ℤ) (hk : k ≠ n) :
      ‖(k : ℂ) * A.moment n k 2 ψ‖ ≤ (|(n : ℝ)| + 1) * ‖a‖ * ‖b k‖ := by
    rw [hrow k hk]
    have he : (k : ℂ) *
        ((sourcePeriodicGapDisplacement hp hp1 ψ k)^3 / ((n-k : ℤ) : ℂ) * a k) =
        ((k : ℂ) / ((n-k : ℤ) : ℂ)) * a k * b k := by rw [hb k]; ring
    rw [he, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (norm_index_ratio_le n k hk)
        (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' a k)
        (norm_nonneg _) (by positivity)) (norm_nonneg _)
  have hs' := hs.subtype (fun k => k ≠ n)
  have hu : Summable (fun k : {k : ℤ // k ≠ n} => ‖(k.val : ℂ) * A.moment n k.val 2 ψ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hbound k.val k.property) hs'
  have hf : (Set.singleton n).Finite := Set.finite_singleton n
  exact hf.summable_compl_iff.mp hu

/-- On a constructed common neighborhood, every weighted second-moment row converges. -/
theorem exists_weighted_moment_summable
    (A : SourceAbelianMomentAtlas hp hp1 W s) (hp3 : p ≤ 3)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        Summable (fun k : ℤ => ‖(k : ℂ) * A.moment n k 2 ψ‖) := by
  obtain ⟨U,hU,hUc,hr,hUV,hlocal⟩ := A.exists_lemma20_3_refined hs hV hrealV
  refine ⟨U,hU,hUc,hr,hUV,?_⟩
  intro ψ hψ n
  obtain ⟨ρ,hρ,_,hrows⟩ := hlocal ψ hψ
  have hhalf : ENNReal.ofReal (p.toReal / 2) ≤ p := by
    conv_rhs => rw [← ENNReal.ofReal_toReal hp]
    exact ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])
  obtain ⟨_,_,hdata⟩ := hrows p hp hp1 hhalf
  obtain ⟨_,_,_,_,hoff⟩ := hdata ψ (mem_ball_self hρ)
  obtain ⟨a,_,_,_,ha⟩ := hoff n
  exact summable_weighted_moment_of_row A hp3 ψ n a ha

/-- The article's candidate weighted moment sum, before physical H₄ identification. -/
def fourthFrequencyCandidate (A : SourceAbelianMomentAtlas hp hp1 W s)
    (n : ℤ) (ψ : CoeffPair p) : ℂ :=
  -12 * ∑' k : ℤ, (k : ℂ) * A.moment n k 2 ψ

/-- Construct the atlas and a common convergence domain; no moment assumptions remain. -/
theorem exists_fourthFrequencyCandidate (hp : p ≠ ⊤) (hp1 : 1 < p) (hp3 : p ≤ 3) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ A : SourceAbelianMomentAtlas hp hp1 W s, ∃ U : Set (CoeffPair p),
        IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ A.domain ∧
        ∀ ψ ∈ U, ∀ n : ℤ,
          Summable (fun k : ℤ => ‖(k : ℂ) * A.moment n k 2 ψ‖) ∧
          HasSum (fun k : ℤ => (-12 : ℂ) * ((k : ℂ) * A.moment n k 2 ψ))
            (fourthFrequencyCandidate A n ψ) := by
  obtain ⟨W,V,_,_,hV,hrealV,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨U,hU,hUc,hreal,hUV,hconv⟩ := exists_weighted_moment_summable A hp3 hs hV hrealV
  refine ⟨W,s,A,U,hU,hUc,hreal,fun ψ hψ => (hUV hψ).1,?_⟩
  intro ψ hψ n
  have ha := hconv ψ hψ n
  exact ⟨ha,ha.of_norm.hasSum.mul_left (-12)⟩

/-- The candidate preserves the established physical coefficient compatibility of moments. -/
theorem fourthFrequencyCandidate_eq_of_coefficients
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {hq : q ≠ ⊤} {hq1 : 1 < q}
    {P : Set (CoeffPair p)} {Y Q : Set (CoeffPair q)}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (A : SourceAbelianMomentAtlas hp hp1 W s) (C : SourceAbelianMomentAtlas hq hq1 Y t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hq hq1 Q t)
    (φ : realTypeSourceSubmodule p) (ψ : realTypeSourceSubmodule q)
    (hc : ∀ j : ℤ, ψ.val.fst j = φ.val.fst j ∧ ψ.val.snd j = φ.val.snd j) (n : ℤ) :
    fourthFrequencyCandidate A n φ.val = fourthFrequencyCandidate C n ψ.val := by
  unfold fourthFrequencyCandidate
  congr 1
  exact tsum_congr (fun k => congrArg ((k : ℂ) * ·)
    (A.moment_real_eq_of_coefficients C hs ht φ ψ hc n k 2))

end NLS.Articles.MKdVBelowL2
