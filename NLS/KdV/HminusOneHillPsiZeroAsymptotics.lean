import NLS.KdV.HminusOneCanonicalHillPsiRealZero
import NLS.KdV.HillRealGapSampleAsymptotics

/-! The actual real zero coefficients have h-minus-one displacement.
For a fixed real source ONE l2 majorant controls ALL numerator indices,
by the two original gap endpoints. This does not assert the finer
squared-gap-over-index bound or uniform complex extensions. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem memlp_hillHminusCanonicalPsiRealZero_inverseIndex_error
    (n : ℕ+) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    Memℓp (fun m : ℕ+ => ((hillHminusCanonicalPsiRealZero n m q hr:ℂ)-
      ((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)) 2 :=
  hillHminusOriginal_real_gap_samples_inverseIndex_error q hr
    (fun m => hillHminusCanonicalPsiRealZero n m q hr)
    (fun m => hillHminusCanonicalPsiRealZero_mem_gap n m q hr)

theorem exists_l2_majorant_ALL_hillHminusCanonicalPsiRealZero
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ A : ℕ+ → ℝ, Memℓp A 2 ∧ (∀ m, 0 ≤ A m) ∧
      ∀ n m : ℕ+, ‖((hillHminusCanonicalPsiRealZero n m q hr:ℂ)-
        ((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖ ≤ A m := by
  let l : ℕ+ → ℝ := fun m => hillHminusLabels q hr (2*(m:ℕ)-1)
  let r : ℕ+ → ℝ := fun m => hillHminusLabels q hr (2*(m:ℕ))
  have hl : Memℓp (fun m : ℕ+ => ((l m:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)) 2 :=
    hillHminusOriginal_real_gap_samples_inverseIndex_error q hr l (fun m =>
      ⟨le_rfl,monotone_hillHminusLabels q hr (by omega)⟩)
  have hright : Memℓp (fun m : ℕ+ => ((r m:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)) 2 :=
    hillHminusOriginal_real_gap_samples_inverseIndex_error q hr r (fun m =>
      ⟨monotone_hillHminusLabels q hr (by omega),le_rfl⟩)
  let A : ℕ+ → ℝ := fun m => ‖((l m:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖+
    ‖((r m:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖
  refine ⟨A,hl.norm.add hright.norm,fun m => add_nonneg (norm_nonneg _) (norm_nonneg _),?_⟩
  intro n m
  let x := hillHminusCanonicalPsiRealZero n m q hr
  let y : ℝ := (Real.pi*(m:ℝ))^2
  have hx : x ∈ Icc (l m) (r m) := hillHminusCanonicalPsiRealZero_mem_gap n m q hr
  have hb : |x-y| ≤ |l m-y|+|r m-y| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (l m-y),abs_nonneg (r m-y),hx.1]
    · linarith [le_abs_self (r m-y),abs_nonneg (l m-y),hx.2]
  have hy : ((Real.pi:ℂ)*(m:ℕ))^2 = (y:ℂ) := by simp only [y,ofReal_pow,ofReal_mul,ofReal_natCast]
  change ‖((x:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖ ≤ _
  dsimp only [A]
  simp only [hy,norm_div,← ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [← add_div]
  exact div_le_div_of_nonneg_right hb (norm_nonneg _)

end NLS.KdV
