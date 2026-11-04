import NLS.SequenceSpaces.NatL2AnalyticRealization

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.Coeff



private def natL2DecodedVector (a : Coeff 2) : ↥(lp (fun _ : ℕ => ℂ) (2 : ℝ≥0∞)) := by
  let f : ℕ → ℂ := fun k => a.val (Equiv.intEquivNat.symm k)
  have hm : Memℓp f 2 := by
    rw [memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)]
    have hs : Summable (fun j : ℤ => ‖a j‖^(2:ℝ≥0∞).toReal) :=
      (lp.memℓp (E := fun _ : ℤ => ℂ) a).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
    exact (Equiv.intEquivNat.symm.summable_iff (f := fun j : ℤ => ‖a j‖^(2:ℝ≥0∞).toReal)).mpr hs
  exact ⟨f,hm⟩

private theorem norm_natL2DecodedVector (a : Coeff 2) : ‖natL2DecodedVector a‖=‖a‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0<(2:ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0<(2:ℝ≥0∞).toReal)]
  congr 1
  exact Equiv.intEquivNat.symm.tsum_eq (fun j : ℤ => ‖a j‖^(2:ℝ≥0∞).toReal)

/-- Transport the fixed integer encoding to the natural-index Hilbert space. -/
def natL2Decode : Coeff 2 →ₗᵢ[ℂ] ↥(lp (fun _ : ℕ => ℂ) (2 : ℝ≥0∞)) where
  toFun := natL2DecodedVector
  map_add' a b := by ext k; rfl
  map_smul' c a := by ext k; rfl
  norm_map' := norm_natL2DecodedVector

theorem natL2Decode_apply (a : Coeff 2) (k : ℕ) :
    natL2Decode a k=a (Equiv.intEquivNat.symm k) := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A finite analytic head and an analytic Hilbert tail assemble into
an actual natural-index Hilbert analytic map, retaining all coordinates. -/
theorem exists_natL2_analytic_head_tail
    (U : Set E) (hU : IsOpen U) (K : ℕ) (a : E → ℕ → ℂ) (T : E → Coeff 2)
    (ha : ∀ k<K, AnalyticOnNhd ℂ (fun x => a x k) U)
    (hT : AnalyticOnNhd ℂ T U) (b : ℕ → ℝ) (M : ℝ)
    (hab : ∀ x∈U, ∀ k<K, ‖a x k‖≤b k)
    (hTb : ∀ x∈U, ‖T x‖^2≤M) :
    ∃ F : E → ↥(lp (fun _ : ℕ => ℂ) (2 : ℝ≥0∞)), AnalyticOnNhd ℂ F U ∧
      (∀ x∈U, ‖F x‖^2≤(∑ k∈Finset.range K, (b k)^2)+M) ∧
      ∀ x∈U, ∀ k : ℕ, F x k=if k<K then a x k else T x (Equiv.intEquivNat.symm (k-K)) := by
  let f : E → ℕ → ℂ := fun x k => if k<K then a x k else T x (Equiv.intEquivNat.symm (k-K))
  have htail (x : E) (k : ℕ) : f x (k+K)=T x (Equiv.intEquivNat.symm k) := by
    simp only [f,not_lt.mpr (Nat.le_add_left K k),if_false,Nat.add_sub_cancel]
  have htailSum (x : E) : Summable (fun k : ℕ => ‖T x (Equiv.intEquivNat.symm k)‖^2) := by
    have hh := (lp.memℓp (natL2Decode (T x))).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,natL2Decode_apply] using hh
  have hnorm (x : E) : (∑' k : ℕ, ‖T x (Equiv.intEquivNat.symm k)‖^2)=‖T x‖^2 := by
    have hh := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) (natL2Decode (T x))
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,natL2Decode_apply,natL2Decode.norm_map] using hh.symm
  have hsum (x : E) : Summable (fun k : ℕ => ‖f x k‖^2) := by
    apply (summable_nat_add_iff K).mp
    simpa only [htail] using htailSum x
  have hbound (x : E) (hx : x∈U) : (∑' k : ℕ, ‖f x k‖^2)≤(∑ k∈Finset.range K, (b k)^2)+M := by
    rw [←Summable.sum_add_tsum_nat_add K (hsum x)]
    simp_rw [htail]
    rw [hnorm]
    apply add_le_add _ (hTb x hx)
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [show f x k=a x k from if_pos hk']
    exact pow_le_pow_left₀ (norm_nonneg _) (hab x hx k hk') 2
  have hf : ∀ k, AnalyticOnNhd ℂ (fun x => f x k) U := by
    intro k
    by_cases hk : k<K
    · simpa only [f,if_pos hk] using ha k hk
    · intro x hx
      have hh := ((lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) 2 (Equiv.intEquivNat.symm (k-K))).analyticAt (T x)).comp (f := T) (hT x hx)
      change AnalyticAt ℂ (fun y => T y (Equiv.intEquivNat.symm (k-K))) x at hh
      simpa only [f,if_neg hk] using hh
  have hFa := analyticOnNhd_natL2OfFunction_of_summable_sq_bound f U hU hf
    ((∑ k∈Finset.range K, (b k)^2)+M) (fun x hx => ⟨hsum x,hbound x hx⟩)
  let F : E → ↥(lp (fun _ : ℕ => ℂ) (2 : ℝ≥0∞)) := fun x => natL2Decode (natL2OfFunction (f x))
  refine ⟨F,(fun x hx => (natL2Decode.toContinuousLinearMap.analyticAt (natL2OfFunction (f x))).comp (f := fun x : E => natL2OfFunction (f x)) (hFa x hx)),?_,?_⟩
  · intro x hx
    change ‖natL2Decode (natL2OfFunction (f x))‖^2≤_
    rw [natL2Decode.norm_map,norm_natL2OfFunction_sq_eq_tsum _ (hsum x)]
    exact hbound x hx
  · intro x _ k
    change natL2OfFunction (f x) (Equiv.intEquivNat.symm k)=f x k
    exact natL2OfFunction_apply_of_summable_sq _ (hsum x) k

end NLS.Coeff
