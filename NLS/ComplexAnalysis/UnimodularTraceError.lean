import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! # Trace error from an approximate eigenvector

For a determinant-one two-by-two matrix, an approximate eigenvector
whose first component is one controls the trace by `m + 1/m`.
-/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem norm_unimodular_trace_error_le (p q s t m v : ℂ)
    (hdet : p*t-q*s = 1) (hm : m ≠ 0)
    (M B E : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hq : ‖q‖ ≤ M) (ht : ‖t‖ ≤ M) (hmb : ‖m‖ ≤ B) (hmi : ‖m⁻¹‖ ≤ B)
    (he : ‖(p+q*v-m,s+t*v-m*v)‖ ≤ E) :
    ‖p+t-(m+m⁻¹)‖ ≤ ((B+2*M)*E)*B := by
  have hid : p+t-(m+m⁻¹) = ((m-t)*(p+q*v-m)+q*(s+t*v-m*v))*m⁻¹ := by
    field_simp
    linear_combination hdet
  have he1 := (norm_fst_le (p+q*v-m,s+t*v-m*v)).trans he
  have he2 := (norm_snd_le (p+q*v-m,s+t*v-m*v)).trans he
  have hmt : ‖m-t‖ ≤ B+M := (norm_sub_le _ _).trans (add_le_add hmb ht)
  have hn : ‖(m-t)*(p+q*v-m)+q*(s+t*v-m*v)‖ ≤ (B+2*M)*E := by
    calc
      _ ≤ ‖m-t‖*‖p+q*v-m‖+‖q‖*‖s+t*v-m*v‖ := by
        simpa only [norm_mul] using norm_add_le ((m-t)*(p+q*v-m)) (q*(s+t*v-m*v))
      _ ≤ (B+M)*E+M*E := add_le_add
        (mul_le_mul hmt he1 (norm_nonneg _) (by positivity))
        (mul_le_mul hq he2 (norm_nonneg _) hM)
      _ = _ := by ring
  rw [hid,norm_mul]
  exact mul_le_mul hn hmi (norm_nonneg _) (by positivity)

end NLS.ComplexAnalysis
