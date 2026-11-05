import NLS.ZakharovShabat.SourceDiagonalNormalizedLaurentBound
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! # The bounded sequence of scaled physical action ratios

Multiplication by 1+|n| removes the inverse-frequency decay. The resulting
actual scalar ratios assemble into a complex analytic bounded sequence.
On every physical real diagonal their real parts have a uniform positive
lower bound, including all collapsed positive gaps.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The physical ratio is the reciprocal of twice a positive spectral
point in the selected gap, with the midpoint used for a closed gap. -/
theorem sourceDiagonalActionRatio_eq_inverse_frequency
    (φ : realDiagonalSourceLocus 2) (n : ℤ) (hn : 0 < n) :
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem _) n).re
      (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem _) n).re,
      0 < ζ ∧ sourceDiagonalActionRatio (by simp) (by norm_num) n φ.val = ((1/(2*ζ) : ℝ) : ℂ) := by
  obtain ⟨U,_,hφU,hUC,_,hone,heq,_⟩ :=
    exists_local_sourceNormalizedDiagonalLaurentAction_eq_contour (by simp) (by norm_num) φ n (ne_of_gt hn)
  let C := (sourceDiagonalLaurentAtlas (by simp) (by norm_num)).localChart φ
  obtain ⟨ζ,hζ,hpos,he⟩ := C.normalizedAction_zero_eq_positive_inverse_mul_one n hn φ (hUC hφU)
  have hne : C.normalizedAction n 1 φ.val ≠ 0 := by
    rw [hone hφU]
    exact sourceNormalizedActionComplexExtension_ne_zero_of_realType (by simp) (by norm_num) n φ.val φ.property.1
  refine ⟨ζ,hζ,hpos,?_⟩
  unfold sourceDiagonalActionRatio
  rw [heq hφU,← hone hφU,he]
  dsimp only [C] at hne he
  push_cast
  field_simp [hne]
  rfl

/-- The positive ratios have a common strictly positive scaled lower bound
at every physical source, even when infinitely many actions vanish. -/
theorem exists_diagonalActionRatio_scaled_re_lower_bound
    (φ : realDiagonalSourceLocus 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℤ, 0 < n →
      c ≤ (((1+|(n : ℝ)| : ℝ) : ℂ)*sourceDiagonalActionRatio (by simp) (by norm_num) n φ.val).re := by
  let d := canonicalPeriodicRightDisplacement (by simp) (by norm_num)
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val)
  let B := Real.pi+‖d‖+1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨1/(2*B),by positivity,?_⟩
  intro n hn
  obtain ⟨ζ,hζ,hpos,hρ⟩ := sourceDiagonalActionRatio_eq_inverse_frequency φ n hn
  have hd : (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem _) n).re-Real.pi*(n : ℝ) ≤ ‖d‖ := by
    have h := (Complex.re_le_norm (d n)).trans (lp.norm_apply_le_norm (by norm_num) d n)
    simpa [d,canonicalPeriodicRightDisplacement_apply] using! h
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb : ζ ≤ B*(1+|(n : ℝ)|) := by
    rw [abs_of_pos hnreal]
    dsimp only [B]
    nlinarith [norm_nonneg d,Real.pi_pos,hζ.2]
  rw [hρ,← ofReal_mul,ofReal_re]
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity : 0 < 2*B) (by positivity : 0 < 2*ζ)).mpr
  nlinarith

def sourceDiagonalScaledActionRatio (n : ℤ) (ψ : CoeffPair 2) : ℂ :=
  if 0 < n then ((1+|(n : ℝ)| : ℝ) : ℂ)*sourceDiagonalActionRatio (by simp) (by norm_num) n ψ else 1

def sourceDiagonalActionRatioSequence (ψ : CoeffPair 2) : Coeff ⊤ :=
  Coeff.ofFunctionOrZero ⊤ (fun n => sourceDiagonalScaledActionRatio n ψ)

/-- All scaled ratios form one actual bounded sequence analytic on a
complex source neighborhood, with no sequence-constructor fallback. -/
theorem exists_local_sourceDiagonalActionRatioSequence_analytic
    (φ : realDiagonalSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      AnalyticOnNhd ℂ sourceDiagonalActionRatioSequence U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, sourceDiagonalActionRatioSequence ψ n = sourceDiagonalScaledActionRatio n ψ := by
  obtain ⟨U,hU,hφU,hA,K,hK,hbound⟩ := exists_local_hilbert_diagonalActionRatio_analytic_inverse_bound φ
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ (sourceDiagonalScaledActionRatio n) U := by
    intro ψ hψ
    change AnalyticAt ℂ (fun χ => if 0 < n then
      ((1+|(n : ℝ)| : ℝ) : ℂ)*sourceDiagonalActionRatio (by simp) (by norm_num) n χ else 1) ψ
    by_cases hn : 0 < n
    · simp only [if_pos hn]
      exact analyticAt_const.mul (hA n (ne_of_gt hn) ψ hψ)
    · simp only [if_neg hn]
      exact analyticAt_const
  have hb (ψ : CoeffPair 2) (hψ : ψ ∈ U) (n : ℤ) :
      ‖sourceDiagonalScaledActionRatio n ψ‖ ≤ max K 1 := by
    by_cases hn : 0 < n
    · rw [sourceDiagonalScaledActionRatio,if_pos hn,norm_mul,Complex.norm_of_nonneg (by positivity)]
      calc
        _ ≤ (1+|(n : ℝ)|)*(K/(1+|(n : ℝ)|)) :=
          mul_le_mul_of_nonneg_left (hbound ψ hψ n (ne_of_gt hn)) (by positivity)
        _ = K := by field_simp
        _ ≤ _ := le_max_left _ _
    · simp only [sourceDiagonalScaledActionRatio,if_neg hn,norm_one]
      exact le_max_right _ _
  have hrealize (ψ : CoeffPair 2) (hψ : ψ ∈ U) :
      ∃ b : Coeff ⊤, (∀ n, b n = sourceDiagonalScaledActionRatio n ψ) ∧ ‖b‖ ≤ max K 1 := by
    let b : Coeff ⊤ := ⟨fun n => sourceDiagonalScaledActionRatio n ψ,
      memℓp_infty ⟨max K 1,by rintro _ ⟨n,rfl⟩; exact hb ψ hψ n⟩⟩
    exact ⟨b,fun _ => rfl,lp.norm_le_of_forall_le (by positivity) (hb ψ hψ)⟩
  obtain ⟨he,hAn⟩ := Coeff.analytic_realization_of_local_bounds
    (fun ψ n => sourceDiagonalScaledActionRatio n ψ) hU hcoord
    (fun ψ hψ => ⟨U,hU,hψ,Subset.rfl,max K 1,hrealize⟩)
  exact ⟨U,hU,hφU,hAn,he⟩

end NLS.ZakharovShabat
