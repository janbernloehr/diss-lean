import NLS.Fourier.PeriodicFourierLebesgueSeries

/-!
# Rudin–Shapiro polynomials on the physical circle

The recursive polynomial pair has pointwise squared energy 2^(n+1).
Its Fourier coefficients have norm one precisely on the integer block
[0, 2^n). Consequently, the first polynomial has uniform norm at most
sqrt(2^(n+1)) and normalized L² square norm exactly 2^n.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal ZeroAtInfty
namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]

/-- The classical polynomial pair, evaluated on the physical circle of period L. -/
def rudinShapiroPair : ℕ → C(AddCircle L,ℂ) × C(AddCircle L,ℂ)
  | 0 => (1,1)
  | n+1 => let pq := rudinShapiroPair n
           (pq.1 + fourier (2^n : ℕ) * pq.2,pq.1 - fourier (2^n : ℕ) * pq.2)

omit [Fact (0 < L)] in
/-- The exact pointwise energy identity for both recursive polynomials. -/
theorem rudinShapiro_energy (n : ℕ) (x : AddCircle L) :
    ‖(rudinShapiroPair (L := L) n).1 x‖^2 + ‖(rudinShapiroPair (L := L) n).2 x‖^2 = 2^(n+1) := by
  induction n with
  | zero => norm_num [rudinShapiroPair]
  | succ n ih =>
    change ‖(rudinShapiroPair (L := L) n).1 x + fourier (2^n : ℕ) x * (rudinShapiroPair (L := L) n).2 x‖^2 +
      ‖(rudinShapiroPair (L := L) n).1 x - fourier (2^n : ℕ) x * (rudinShapiroPair (L := L) n).2 x‖^2 = _
    rw [parallelogram_law_with_norm ℂ,norm_mul]
    simp only [fourier_apply,Circle.norm_coe,one_mul]
    rw [ih,pow_succ]
    ring

/-- The square-root uniform bound used in the non-surjectivity argument. -/
theorem norm_rudinShapiro_le (n : ℕ) :
    ‖(rudinShapiroPair (L := L) n).1‖ ≤ Real.sqrt (2^(n+1)) := by
  apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).mpr
  intro x
  have h := rudinShapiro_energy n x
  have hs := Real.sq_sqrt (show 0 ≤ (2:ℝ)^(n+1) by positivity)
  have hp := sq_nonneg ‖(rudinShapiroPair (L := L) n).2 x‖
  nlinarith [Real.sqrt_nonneg ((2:ℝ)^(n+1)),norm_nonneg ((rudinShapiroPair (L := L) n).1 x)]

/-- Multiplication by a physical Fourier mode shifts the coefficient index. -/
theorem fourierCoeff_fourier_mul (m n : ℤ) (f : C(AddCircle L,ℂ)) :
    fourierCoeff (fourier m * f : C(AddCircle L,ℂ)) n = fourierCoeff f (n-m) := by
  simp only [fourierCoeff,ContinuousMap.mul_apply,smul_eq_mul]
  congr 1
  funext x
  rw [← mul_assoc,← fourier_add]
  rw [show -n + m = -(n-m) by omega]

theorem fourierCoeff_continuous_add (f g : C(AddCircle L,ℂ)) (n : ℤ) :
    fourierCoeff (f+g) n = fourierCoeff f n + fourierCoeff g n := by
  rw [ContinuousMap.coe_add,fourierCoeff.add
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  rfl

theorem fourierCoeff_continuous_sub (f g : C(AddCircle L,ℂ)) (n : ℤ) :
    fourierCoeff (f-g) n = fourierCoeff f n - fourierCoeff g n := by
  rw [sub_eq_add_neg,fourierCoeff_continuous_add,show -g = (-1:ℂ) • g by simp]
  rw [ContinuousMap.coe_smul,fourierCoeff.const_smul]
  simp [sub_eq_add_neg]

theorem rudinShapiro_coeff_succ (n : ℕ) (k : ℤ) :
    fourierCoeff (rudinShapiroPair (L := L) (n+1)).1 k =
      fourierCoeff (rudinShapiroPair (L := L) n).1 k + fourierCoeff (rudinShapiroPair (L := L) n).2 (k-(2^n:ℕ)) ∧
    fourierCoeff (rudinShapiroPair (L := L) (n+1)).2 k =
      fourierCoeff (rudinShapiroPair (L := L) n).1 k - fourierCoeff (rudinShapiroPair (L := L) n).2 (k-(2^n:ℕ)) := by
  simp only [rudinShapiroPair,fourierCoeff_continuous_add,fourierCoeff_continuous_sub,fourierCoeff_fourier_mul]
  exact ⟨trivial,trivial⟩

/-- Both polynomials have unit coefficient norms exactly on [0, 2^n). -/
theorem rudinShapiro_coeff_norm (n : ℕ) (k : ℤ) :
    ‖fourierCoeff (rudinShapiroPair (L := L) n).1 k‖ = (if 0 ≤ k ∧ k < (2^n:ℕ) then 1 else 0) ∧
    ‖fourierCoeff (rudinShapiroPair (L := L) n).2 k‖ = (if 0 ≤ k ∧ k < (2^n:ℕ) then 1 else 0) := by
  induction n generalizing k with
  | zero =>
    have he : (1 : C(AddCircle L,ℂ)) = fourier 0 := by ext x; simp
    simp only [rudinShapiroPair,he,fourierCoeff_fourier,Pi.single_apply]
    by_cases hk : k = 0
    · simp [hk]
    · have hn : ¬(0 ≤ k ∧ k < (2^0:ℕ)) := by norm_num; omega
      simp only [if_neg hk,norm_zero,if_neg hn]
      exact ⟨trivial,trivial⟩
  | succ n ih =>
    obtain ⟨hP,hQ⟩ := rudinShapiro_coeff_succ (L := L) n k
    rw [hP,hQ]
    have hpow : ((2^(n+1):ℕ):ℤ) = (2^n:ℕ)+(2^n:ℕ) := by push_cast; ring
    have hpos : (0:ℤ) < (2^n:ℕ) := by positivity
    by_cases hlo : 0 ≤ k ∧ k < (2^n:ℕ)
    · have hshift : ¬(0 ≤ k-(2^n:ℕ) ∧ k-(2^n:ℕ) < (2^n:ℕ)) := by omega
      have hz : fourierCoeff (rudinShapiroPair (L := L) n).2 (k-(2^n:ℕ)) = 0 :=
        norm_eq_zero.mp (by simpa only [if_neg hshift] using (ih (k-(2^n:ℕ))).2)
      have htotal : 0 ≤ k ∧ k < (2^(n+1):ℕ) := by rw [hpow]; omega
      simp only [hz,add_zero,sub_zero,if_pos htotal]
      constructor <;> simpa only [if_pos hlo] using (ih k).1
    · have hz : fourierCoeff (rudinShapiroPair (L := L) n).1 k = 0 :=
        norm_eq_zero.mp (by simpa only [if_neg hlo] using (ih k).1)
      have hiff : (0 ≤ k-(2^n:ℕ) ∧ k-(2^n:ℕ) < (2^n:ℕ)) ↔ (0 ≤ k ∧ k < (2^(n+1):ℕ)) := by
        rw [hpow]
        omega
      simp only [hz,zero_add,zero_sub,norm_neg]
      constructor <;> simpa only [hiff] using (ih (k-(2^n:ℕ))).2

/-- Parseval gives exactly 2^n for the squared L² norm with probability Haar measure. -/
theorem integral_sq_rudinShapiro (n : ℕ) :
    (∫ x, ‖(rudinShapiroPair (L := L) n).1 x‖^2 ∂AddCircle.haarAddCircle) = (2:ℝ)^n := by
  let f := ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (rudinShapiroPair (L := L) n).1
  have hc (k : ℤ) : ‖fourierCoeff f k‖ = if 0 ≤ k ∧ k < (2^n:ℕ) then 1 else 0 := by
    rw [show fourierCoeff f k = fourierCoeff (rudinShapiroPair (L := L) n).1 k by
      exact congrFun (fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _)) k]
    exact (rudinShapiro_coeff_norm n k).1
  have he : (∑' k : ℤ, ‖fourierCoeff f k‖^2) = (2:ℝ)^n := by
    rw [tsum_eq_sum (s := Finset.Ico (0:ℤ) (2^n:ℕ))]
    · simp only [hc]
      calc
        _ = ∑ _k ∈ Finset.Ico (0:ℤ) (2^n:ℕ), (1:ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [if_pos (Finset.mem_Ico.mp hk),one_pow]
        _ = _ := by
          simp only [Finset.sum_const,Int.card_Ico,sub_zero,nsmul_eq_mul,mul_one]
          have hnonneg : (0:ℤ) ≤ 2^n := by positivity
          exact_mod_cast Int.toNat_of_nonneg hnonneg
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      rw [hc,if_neg hk,zero_pow (by norm_num)]
  have h := (hasSum_sq_fourierCoeff f).tsum_eq
  rw [he] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    (rudinShapiroPair (L := L) n).1] with x hx
  dsimp [f] at *
  rw [hx]

end NLS.Fourier
