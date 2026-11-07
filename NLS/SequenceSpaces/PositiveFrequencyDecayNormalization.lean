import NLS.SequenceSpaces.Basic
import Mathlib.Topology.Algebra.Order.Field

/-! Literal scalar normalization and original positive frequency labels
preserve both a uniform weighted bound and a vanishing weighted tail. -/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.Coeff

theorem scaled_positive_frequency_bound
    (w : ℤ → ℝ) (a : ℤ → ℂ) (f : ℕ+ → ℂ) (c : ℂ)
    (hcal : ∀ n : ℕ+, f n=c*a (n : ℤ))
    (K : ℝ) (hb : ∀ n : ℤ, w n*‖a n‖≤K) (n : ℕ+) :
    w (n : ℤ)*‖f n‖≤‖c‖*K := by
  rw [hcal,norm_mul,←mul_assoc,mul_comm (w (n : ℤ)) ‖c‖,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _)

theorem tendsto_scaled_positive_frequency
    (w : ℤ → ℝ) (a : ℤ → ℂ) (f : ℕ+ → ℂ) (c : ℂ)
    (hcal : ∀ n : ℕ+, f n=c*a (n : ℤ))
    (ha : Tendsto (fun n : ℕ => w (n : ℤ)*‖a (n : ℤ)‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => w ((n+1 : ℕ) : ℤ)*‖f ⟨n+1,by omega⟩‖) atTop (𝓝 0) := by
  have ht := (ha.comp (tendsto_add_atTop_nat 1)).const_mul ‖c‖
  rw [mul_zero] at ht
  apply ht.congr'
  exact Filter.Eventually.of_forall (fun n => by
    have he : ‖f (⟨n+1,by omega⟩ : ℕ+)‖=‖c‖*‖a ((n+1 : ℕ) : ℤ)‖ :=
      (congrArg norm (hcal (⟨n+1,by omega⟩ : ℕ+))).trans (norm_mul _ _)
    exact (mul_left_comm ‖c‖ (w ((n+1 : ℕ) : ℤ)) ‖a ((n+1 : ℕ) : ℤ)‖).trans
      (congrArg (fun x : ℝ => w ((n+1 : ℕ) : ℤ)*x) he).symm)

end NLS.Coeff
