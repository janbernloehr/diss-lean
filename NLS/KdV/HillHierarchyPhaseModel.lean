import NLS.ComplexAnalysis.LaurentContourCoefficient
import NLS.ComplexAnalysis.WeightedSquareRemainder
import NLS.KdV.HillHierarchyTraceCoefficient
import NLS.KdV.HillHierarchyPhase

/-! # The exact finite physical hierarchy phase-square model and its source trace coefficient. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ContDiff ComplexConjugate
namespace NLS.KdV
open NLS.ComplexAnalysis
def hillSourceSquaredPhaseModel (H : ℕ → ℂ) (M : ℕ) (z : ℂ) : ℂ :=
  (-1)*z^(1 : ℤ)+
    (∑ i ∈ Finset.range M, (2*(H i/4^(i+1)))*z^(-((i+1 : ℕ) : ℤ))) -
    ∑ ij ∈ Finset.range M ×ˢ Finset.range M,
      ((H ij.1/4^(ij.1+1))*(H ij.2/4^(ij.2+1)))*z^(-((ij.1+ij.2+3 : ℕ) : ℤ))

theorem normalized_hillSourceSquaredPhaseModel_circle (H : ℕ → ℂ) (M m : ℕ)
    (hm : m < M) (R : ℝ) (hR : 0 < R) :
    ((Real.pi : ℂ)*I)⁻¹ *
      (∮ z in C((0 : ℂ),R), z^m*hillSourceSquaredPhaseModel H M z) =
        hillHierarchyTraceCoefficient H m := by
  let a : ℕ → ℂ := fun i => H i/4^(i+1)
  let S := Finset.range M ×ˢ Finset.range M
  have h0 := circleIntegrable_weighted_zpow (-1) 1 m R hR
  have h1 : CircleIntegrable (fun z : ℂ => z^m*
      (∑ i ∈ Finset.range M, (2*a i)*z^(-((i+1 : ℕ) : ℤ)))) 0 R := by
    convert! CircleIntegrable.sum (Finset.range M)
      (fun i _ => circleIntegrable_weighted_zpow (2*a i) (-((i+1 : ℕ) : ℤ)) m R hR) using 1
    funext z
    simp only [Finset.mul_sum, Finset.sum_apply]
  have h2 : CircleIntegrable (fun z : ℂ => z^m*
      (∑ ij ∈ S, (a ij.1*a ij.2)*z^(-((ij.1+ij.2+3 : ℕ) : ℤ)))) 0 R := by
    convert! CircleIntegrable.sum S
      (fun ij _ => circleIntegrable_weighted_zpow (a ij.1*a ij.2)
        (-((ij.1+ij.2+3 : ℕ) : ℤ)) m R hR) using 1
    funext z
    simp only [Finset.mul_sum, Finset.sum_apply]
  have h01 : CircleIntegrable (fun z : ℂ => z^m*((-1)*z^(1 : ℤ))+z^m*
      (∑ i ∈ Finset.range M, (2*a i)*z^(-((i+1 : ℕ) : ℤ)))) 0 R := h0.add h1
  have he : (fun z : ℂ => z^m*hillSourceSquaredPhaseModel H M z) =
      fun z => (z^m*((-1)*z^(1 : ℤ))+z^m*
        (∑ i ∈ Finset.range M, (2*a i)*z^(-((i+1 : ℕ) : ℤ))))-
        z^m*(∑ ij ∈ S, (a ij.1*a ij.2)*z^(-((ij.1+ij.2+3 : ℕ) : ℤ))) := by
    funext z
    simp only [hillSourceSquaredPhaseModel, a, S, mul_sub, mul_add]
  rw [he, circleIntegral.integral_sub h01 h2, circleIntegral.integral_add h0 h1,
    mul_sub, mul_add, normalized_circleIntegral_weighted_zpow (-1) 1 m R hR,
    normalized_circleIntegral_weighted_finsum _ _ _ m R hR,
    normalized_circleIntegral_weighted_finsum _ _ _ m R hR]
  have hf : ¬(m : ℤ)+1 = -1 := by omega
  have hsingle : (∑ i ∈ Finset.range M,
      if (m : ℤ)+(-((i+1 : ℕ) : ℤ)) = -1 then 2*(2*a i) else 0) = 4*a m := by
    have ht (i : ℕ) : ((m : ℤ)+(-((i+1 : ℕ) : ℤ)) = -1) ↔ i=m := by omega
    simp only [ht]
    simp [Finset.mem_range.mpr hm]
    ring
  rw [if_neg hf, zero_add, hsingle]
  rcases m with _ | _ | n
  · have hzero : (∑ ij ∈ S, if ((0 : ℕ) : ℤ)+(-((ij.1+ij.2+3 : ℕ) : ℤ)) = -1
        then 2*(a ij.1*a ij.2) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro ij _
      rw [if_neg (by omega)]
    rw [hzero, sub_zero, hillHierarchyTraceCoefficient_zero]
    dsimp only [a]
    norm_num
    ring
  · have hzero : (∑ ij ∈ S, if ((0+1 : ℕ) : ℤ)+(-((ij.1+ij.2+3 : ℕ) : ℤ)) = -1
        then 2*(a ij.1*a ij.2) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro ij _
      rw [if_neg (by omega)]
    rw [hzero, sub_zero]
    simp only [Nat.zero_add, hillHierarchyTraceCoefficient_one]
    dsimp only [a]
    norm_num
    ring
  · have ht (ij : ℕ × ℕ) :
        (((n+1+1 : ℕ) : ℤ)+(-((ij.1+ij.2+3 : ℕ) : ℤ)) = -1) ↔ ij.1+ij.2=n := by omega
    simp only [ht]
    rw [sum_rectangle_ite_eq_antidiagonal M n (by omega), ← Finset.mul_sum]
    have hconv : (∑ ij ∈ Finset.antidiagonal n, a ij.1*a ij.2) =
        (∑ ij ∈ Finset.antidiagonal n, H ij.1*H ij.2)/4^(n+2) := by
      simpa only [hillFormalHamiltonianSeries, PowerSeries.coeff_mul, PowerSeries.coeff_mk, a] using
        hillFormalHamiltonianSeries_square_coeff H n
    rw [hconv]
    simp only [hillHierarchyTraceCoefficient, show 2 ≤ n+1+1 by omega, ↓reduceIte,
      show n+1+1-2 = n by omega]
    dsimp only [a]
    rw [show n+1+1+1 = (n+2)+1 by omega, pow_succ]
    ring


def hillFiniteSourcePhase (H : ℕ → ℂ) (M : ℕ) (z : ℂ) : ℂ :=
  -I*z+I*(∑ i ∈ Finset.range M, (H i/4^(i+1))/z^(2*i+3))

theorem hillFiniteSourcePhase_square (H : ℕ → ℂ) (M : ℕ) (z : ℂ) (hz : z ≠ 0) :
    hillFiniteSourcePhase H M z ^ 2 = hillSourceSquaredPhaseModel H M (z^2) := by
  let a : ℕ → ℂ := fun i => H i/4^(i+1)
  let S := ∑ i ∈ Finset.range M, a i/z^(2*i+3)
  have hone : (∑ i ∈ Finset.range M, (2*a i)*(z^2)^(-((i+1 : ℕ) : ℤ))) = 2*z*S := by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hp : z^(2*i+3) = z*(z^2)^(i+1) := by
      rw [show 2*i+3 = 2*(i+1)+1 by omega, pow_add, pow_mul]
      ring
    rw [hp]
    simp only [zpow_neg, zpow_natCast]
    field_simp
  have htwo : (∑ ij ∈ Finset.range M ×ˢ Finset.range M,
      (a ij.1*a ij.2)*(z^2)^(-((ij.1+ij.2+3 : ℕ) : ℤ))) = S^2 := by
    dsimp only [S]
    rw [Finset.sum_product]
    conv_rhs => rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hp : z^(2*i+3)*z^(2*j+3) = (z^2)^(i+j+3) := by
      rw [← pow_add, ← pow_mul]
      congr 1
      omega
    conv_rhs => rw [div_mul_div_comm, hp]
    simp only [zpow_neg, zpow_natCast, div_eq_mul_inv]
  change (-I*z+I*S)^2 = _
  change _ = (-1)*(z^2)^(1 : ℤ)+
    (∑ i ∈ Finset.range M, (2*a i)*(z^2)^(-((i+1 : ℕ) : ℤ))) -
    ∑ ij ∈ Finset.range M ×ˢ Finset.range M,
      (a ij.1*a ij.2)*(z^2)^(-((ij.1+ij.2+3 : ℕ) : ℤ))
  rw [hone, htwo, zpow_one]
  ring_nf
  rw [I_sq]
  ring


theorem norm_hillFiniteSourcePhase_le (H : ℕ → ℂ) (M : ℕ) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖hillFiniteSourcePhase H M z‖ ≤
      (1+∑ i ∈ Finset.range M, ‖H i/4^(i+1)‖)*‖z‖ := by
  have hs : ‖∑ i ∈ Finset.range M, (H i/4^(i+1))/z^(2*i+3)‖ ≤
      ∑ i ∈ Finset.range M, ‖H i/4^(i+1)‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    simpa only [pow_zero, one_mul] using
      norm_weighted_laurent_term_le z (H i/4^(i+1)) hz 0 (2*i+3) (by omega)
  have ht := norm_add_le (-I*z) (I*(∑ i ∈ Finset.range M, (H i/4^(i+1))/z^(2*i+3)))
  simp only [norm_mul, norm_neg, norm_I, one_mul] at ht
  change ‖-I*z+I*(∑ i ∈ Finset.range M, (H i/4^(i+1))/z^(2*i+3))‖ ≤ _
  have hsum : 0 ≤ ∑ i ∈ Finset.range M, ‖H i/4^(i+1)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith

theorem norm_hillSquaredPhaseModel_error (H : ℕ → ℂ) (M : ℕ) (z F : ℂ) (D : ℝ)
    (hz : 1 ≤ ‖z‖) (hD : 0 ≤ D)
    (herror : ‖z‖^(2*M+1)*‖F-hillFiniteSourcePhase H M z‖ ≤ D) :
    ‖z‖^(2*M)*‖F^2-hillSourceSquaredPhaseModel H M (z^2)‖ ≤
      D*(2*(1+∑ i ∈ Finset.range M, ‖H i/4^(i+1)‖)+D) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [← hillFiniteSourcePhase_square H M z hz0]
  exact norm_square_error_of_phase_error_general (2*M) F (hillFiniteSourcePhase H M z) z D _
    hz hD (by positivity) (norm_hillFiniteSourcePhase_le H M z hz) herror

theorem hillHamiltonianPhase_mean_zero (q : ℝ → ℂ)
    (hmean : (∫ x in (0 : ℝ)..1, q x) = 0) (M : ℕ) (z : ℂ) :
    hillHamiltonianPhase q M z = hillFiniteSourcePhase (classicalKdVHierarchyHamiltonian q) M z := by
  unfold hillHamiltonianPhase hillFiniteSourcePhase
  rw [hmean]
  simp only [mul_zero, zero_div, add_zero]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [div_mul_eq_div_div]
  ring


theorem hillSourceSquaredPhaseModel_conj (H : ℕ → ℂ) (hH : ∀ m, conj (H m) = H m)
    (M : ℕ) (z : ℂ) :
    hillSourceSquaredPhaseModel H M (conj z) = conj (hillSourceSquaredPhaseModel H M z) := by
  have h2 : conj (2 : ℂ) = 2 := by apply Complex.ext <;> norm_num
  have h4 : conj (4 : ℂ) = 4 := by apply Complex.ext <;> norm_num
  simp [hillSourceSquaredPhaseModel, hH, h2, h4]


theorem circleIntegrable_hillSourceSquaredPhaseModel (H : ℕ → ℂ) (M m : ℕ)
    (R : ℝ) (hR : 0 < R) :
    CircleIntegrable (fun z => z^m*hillSourceSquaredPhaseModel H M z) 0 R := by
  have h0 := circleIntegrable_weighted_zpow (-1) 1 m R hR
  have h1 := circleIntegrable_weighted_finsum (Finset.range M)
    (fun i => 2*(H i/4^(i+1))) (fun i => -((i+1 : ℕ) : ℤ)) m R hR
  have h2 := circleIntegrable_weighted_finsum (Finset.range M ×ˢ Finset.range M)
    (fun ij => (H ij.1/4^(ij.1+1))*(H ij.2/4^(ij.2+1)))
    (fun ij => -((ij.1+ij.2+3 : ℕ) : ℤ)) m R hR
  convert (h0.add h1).sub h2 using 1
  funext z
  simp only [hillSourceSquaredPhaseModel, Pi.sub_apply, Pi.add_apply, mul_sub, mul_add]


def hillClassicalHierarchyTraceValue (q : ℝ → ℂ) (m : ℕ) : ℂ :=
  hillHierarchyTraceCoefficient (classicalKdVHierarchyHamiltonian q) m


end NLS.KdV
