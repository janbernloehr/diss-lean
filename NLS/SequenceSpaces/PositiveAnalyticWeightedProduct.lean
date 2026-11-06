import NLS.SequenceSpaces.PositiveFourierInverseMajorant
import NLS.SequenceSpaces.BoundedCoordinateAnalytic
import NLS.SequenceSpaces.Weighted

/-! # Native weighted positive products of analytic Hilbert sequences -/
noncomputable section
open Set Metric Filter Topology
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def positiveWeightedProduct (w : Weight) (m : E → ℕ+ → ℂ) (a : E → Coeff 2) (u : E) : WeightedCoeff w 2 :=
  (WeightedCoeff.weightIsometry w 2).symm
    (positiveFamilySequence (fun k => (w (k : ℤ) : ℂ)*m u k*a u (k : ℤ)))

theorem positiveWeightedProduct_analytic_bound (w : Weight) (m : E → ℕ+ → ℂ) (a : E → Coeff 2)
    {U : Set E} (hU : IsOpen U) (ha : AnalyticOnNhd ℂ a U)
    (hm : ∀ k : ℕ+, AnalyticOnNhd ℂ (fun u => m u k) U)
    (C N : ℝ) (hC : 0 ≤ C)
    (hmb : ∀ u ∈ U, ∀ k : ℕ+, w (k : ℤ)*‖m u k‖ ≤ C)
    (hab : ∀ u ∈ U, ‖a u‖ ≤ N) :
    AnalyticOnNhd ℂ (positiveWeightedProduct w m a) U ∧
    ∀ u ∈ U, ‖positiveWeightedProduct w m a u‖ ≤ 2*C*‖a u‖ ∧
      (∀ k : ℕ+, (positiveWeightedProduct w m a u).val (k : ℤ) = m u k*a u (k : ℤ)) ∧
      ∀ j : ℤ, j ≤ 0 → (positiveWeightedProduct w m a u).val j = 0 := by
  let f := fun (u : E) (k : ℕ+) => (w (k : ℤ) : ℂ)*m u k*a u (k : ℤ)
  let G := fun u => positiveFamilySequence (f u)
  have hpoint (u : E) (hu : u ∈ U) (k : ℕ+) :
      ‖f u k‖ ≤ C*(‖a u (k : ℤ)‖+‖a u (-(k : ℤ))‖+0/(k : ℝ)) := by
    dsimp only [f]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive _)]
    have h := mul_le_mul_of_nonneg_right (hmb u hu k) (norm_nonneg (a u (k : ℤ)))
    apply h.trans
    simp only [zero_div,add_zero]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) hC
  have hmem (u : E) (hu : u ∈ U) := positiveFamilySequence_bound (f u) (a u) C 0 hC (by norm_num) (hpoint u hu)
  have hval (u : E) (hu : u ∈ U) (j : ℤ) : G u j = positiveFamilyCoordinates (f u) j :=
    ofFunctionOrZero_apply_of_mem 2 _ (hmem u hu).1 j
  have hb (u : E) (hu : u ∈ U) : ‖G u‖ ≤ 2*C*N := by
    apply (hmem u hu).2.trans
    calc
      _ = 2*C*‖a u‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hab u hu) (mul_nonneg (by norm_num) hC)
  have hfa (k : ℕ+) : AnalyticOnNhd ℂ (fun u => f u k) U := by
    intro u hu
    exact (analyticAt_const.mul (hm k u hu)).mul
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).analyticAt (a u)).comp (ha u hu))
  have hcoord (j : ℤ) : AnalyticOnNhd ℂ (fun u => G u j) U := by
    intro u hu
    by_cases hj : 0 < j
    · apply (hfa (positivePoleIndex j hj) u hu).congr
      filter_upwards [hU.mem_nhds hu] with v hv
      rw [hval v hv,positiveFamilyCoordinates,dif_pos hj]
    · apply (analyticAt_const (v := (0 : ℂ))).congr
      filter_upwards [hU.mem_nhds hu] with v hv
      rw [hval v hv,positiveFamilyCoordinates,dif_neg hj]
  have hGa := analyticOnNhd_of_bounded_coordinatewise G hU hcoord (2*C*N) hb
  refine ⟨?_,?_⟩
  · intro u hu
    exact (((WeightedCoeff.weightIsometry w 2).symm.toContinuousLinearEquiv.toContinuousLinearMap).analyticAt _).comp
      (hGa u hu)
  · intro u hu
    refine ⟨?_,?_,?_⟩
    · change ‖(WeightedCoeff.weightIsometry w 2).symm (G u)‖ ≤ _
      rw [LinearIsometryEquiv.norm_map]
      exact (hmem u hu).2.trans_eq (by ring)
    · intro k
      change G u (k : ℤ)/(w (k : ℤ) : ℂ) = _
      rw [hval u hu,positiveFamilyCoordinates_nat]
      dsimp only [f]
      field_simp [w.complex_ne_zero]
    · intro j hj
      change G u j/(w j : ℂ) = _
      rw [hval u hu,positiveFamilyCoordinates,dif_neg (by omega : ¬ 0 < j),zero_div]

end NLS.Coeff
