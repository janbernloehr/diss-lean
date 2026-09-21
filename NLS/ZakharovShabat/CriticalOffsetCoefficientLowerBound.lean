import NLS.ZakharovShabat.UniformSmallCriticalValues
import NLS.ZakharovShabat.CriticalOffsetCoefficient

/-! # Uniform nonvanishing of the critical midpoint coefficient
Uniformly small remaining-product errors and the locally bounded midpoint
offset make the coefficient approach two. A common distant tail therefore
has coefficient norm at least one, justifying division in Lemma 8.6.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual midpoint coefficient tends to two locally uniformly at large signed indices. -/
theorem exists_uniform_small_criticalOffsetCoefficient_error (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0, ∀ n : ℤ, N < n.natAbs →
        ‖canonicalCriticalOffsetCoefficient hp hp1 ψ heven n-2‖ ≤ ε := by
  obtain ⟨V,hvo,hvc,hvφ,hv0,R,hR,hbound⟩ := exists_uniform_canonicalCriticalMidpointOffset_bound hp hp1 φ
  have hden : 0 < 2+R := by linarith
  obtain ⟨N,hN,W,hwo,hwc,hwφ,hw0,hsmall⟩ := exists_uniform_small_deletedProduct_critical_values hp hp1 φ
    (div_pos hε hden)
  refine ⟨N,hN,V ∩ W,hvo.inter hwo,hvc.inter hwc,⟨hvφ,hwφ⟩,⟨hv0,hw0⟩,fun ψ hψ heven n hn => ?_⟩
  obtain ⟨hv,hd⟩ := hsmall ψ hψ.2 heven n hn
  have ha : ‖canonicalCriticalMidpointOffset hp hp1 ψ heven n‖ ≤ R :=
    (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ n).trans (hbound ψ hψ.1 heven)
  rw [canonicalCriticalOffsetCoefficient_sub_two]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_ofNat]
  calc
    _ ≤ 2*(ε/(2+R))+R*(ε/(2+R)) :=
      add_le_add (mul_le_mul_of_nonneg_left hv (by norm_num)) (mul_le_mul ha hd (norm_nonneg _) hR)
    _ = ε := by field_simp

/-- On one common distant tail the midpoint coefficient has norm at least one. -/
theorem exists_uniform_criticalOffsetCoefficient_lower_bound (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0, ∀ n : ℤ, N < n.natAbs →
        1 ≤ ‖canonicalCriticalOffsetCoefficient hp hp1 ψ heven n‖ := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,h⟩ := exists_uniform_small_criticalOffsetCoefficient_error hp hp1 φ zero_lt_one
  refine ⟨N,hN,U,ho,hc,hφ,h0,fun ψ hψ heven n hn => ?_⟩
  have he := norm_le_norm_sub_add (2 : ℂ) (canonicalCriticalOffsetCoefficient hp hp1 ψ heven n)
  rw [norm_sub_rev] at he
  norm_num only [Complex.norm_ofNat] at he
  linarith [h ψ hψ heven n hn]

/-- The nonzero coefficient gives the exact squared-gap quotient, including collapsed gaps. -/
theorem canonicalCriticalMidpointOffset_eq_gap_sq_mul_quotient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (n : ℤ)
    (hne : canonicalCriticalOffsetCoefficient hp hp1 φ heven n ≠ 0) :
    canonicalCriticalMidpointOffset hp hp1 φ heven n =
      (canonicalPeriodicGap hp hp1 φ heven n)^2*
        (canonicalDeletedCriticalDerivative hp hp1 φ heven n/(4*canonicalCriticalOffsetCoefficient hp hp1 φ heven n)) := by
  apply mul_left_cancel₀ hne
  rw [canonicalCriticalOffsetCoefficient_identity]
  field_simp

end NLS.ZakharovShabat
