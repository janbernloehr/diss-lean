import NLS.ZakharovShabat.SourceFiniteGapWeightedRegularity
import NLS.SequenceSpaces.SobolevDerivative
import NLS.SequenceSpaces.SobolevEmbedding

/-! # Sobolev regularity of real finite-gap sources

Iterate a fixed positive weighted gain while preserving the original
source coefficients. This gives every nonnegative Sobolev weight at
the original exponent and, by the one-derivative embedding, `H¹`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Iterating the weighted bootstrap gives every nonnegative Sobolev
weight on the physical period-two realization of a finite-gap source. -/
theorem sourceFiniteGap_physical_mem_sobolev
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) (s : ℝ) (_hs : 0 ≤ s) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*Coeff.periodDouble φ.val.fst n) p ∧
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*Coeff.periodDouble φ.val.snd n) p := by
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hp0 : 0 < p.toReal := zero_lt_one.trans hpR
  let α := min 1 (p.toReal-1)
  let δ := α/(2*p.toReal)
  have hα : 0 < α := lt_min (by norm_num) (by linarith)
  have hδ : 0 < δ := div_pos hα (by positivity)
  have hδp : δ*p.toReal < min 1 (p.toReal-1) := by
    have he : δ*p.toReal = α/2 := by dsimp [δ]; field_simp
    rw [he]
    change α/2 < α
    linarith
  have hstep (t : ℝ) (ht : 0 ≤ t)
      (h : Memℓp (fun n => (Weight.sobolev t n : ℂ)*Coeff.periodDouble φ.val.fst n) p ∧
        Memℓp (fun n => (Weight.sobolev t n : ℂ)*Coeff.periodDouble φ.val.snd n) p) :
      Memℓp (fun n => (Weight.sobolev (t+δ) n : ℂ)*Coeff.periodDouble φ.val.fst n) p ∧
      Memℓp (fun n => (Weight.sobolev (t+δ) n : ℂ)*Coeff.periodDouble φ.val.snd n) p := by
    let w := SpectralWeight.sobolev t ht
    let a : WeightedCoeff w.toWeight p := ⟨Coeff.periodDouble φ.val.fst, by
      change Memℓp (fun n => (w n : ℂ)*Coeff.periodDouble φ.val.fst n) p
      simpa only [w,SpectralWeight.sobolev_apply] using h.1⟩
    let b : WeightedCoeff w.toWeight p := ⟨Coeff.periodDouble φ.val.snd, by
      change Memℓp (fun n => (w n : ℂ)*Coeff.periodDouble φ.val.snd n) p
      simpa only [w,SpectralWeight.sobolev_apply] using h.2⟩
    let ψ : WeightedCoeffPair w.toWeight p := WithLp.toLp p (a,b)
    have hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val := by
      apply weightedPair_ext
      · intro n
        exact (SpectralWeight.forgetWeight_apply w a n).trans (sourceWeightedPeriodOne_fst φ.val n).symm
      · intro n
        exact (SpectralWeight.forgetWeight_apply w b n).trans (sourceWeightedPeriodOne_snd φ.val n).symm
    have hg := sourceFiniteGap_weighted_mem_sobolev hp hp1 φ hfinite w ψ hψ δ hδ.le hδp
    change Memℓp (fun n => (Weight.sobolev δ n : ℂ)*((w n : ℂ)*Coeff.periodDouble φ.val.fst n)) p ∧
      Memℓp (fun n => (Weight.sobolev δ n : ℂ)*((w n : ℂ)*Coeff.periodDouble φ.val.snd n)) p at hg
    simpa only [w,SpectralWeight.sobolev_apply,Weight.sobolev_add,Complex.ofReal_mul,
      mul_assoc,mul_left_comm,mul_comm] using hg
  have hall (k : ℕ) :
      Memℓp (fun n => (Weight.sobolev ((k : ℝ)*δ) n : ℂ)*Coeff.periodDouble φ.val.fst n) p ∧
      Memℓp (fun n => (Weight.sobolev ((k : ℝ)*δ) n : ℂ)*Coeff.periodDouble φ.val.snd n) p := by
    induction k with
    | zero =>
      simp only [Nat.cast_zero,zero_mul,Weight.sobolev_zero_apply,Complex.ofReal_one,one_mul]
      exact ⟨lp.memℓp (Coeff.periodDouble φ.val.fst),lp.memℓp (Coeff.periodDouble φ.val.snd)⟩
    | succ k ih =>
      simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hstep ((k : ℝ)*δ) (by positivity) ih
  obtain ⟨K,hK⟩ := exists_nat_gt (s/δ)
  have hKs : s ≤ (K : ℝ)*δ := ((div_lt_iff₀ hδ).mp hK).le
  have hmono (a : Coeff p)
      (ha : Memℓp (fun n => (Weight.sobolev ((K : ℝ)*δ) n : ℂ)*a n) p) :
      Memℓp (fun n => (Weight.sobolev s n : ℂ)*a n) p := by
    apply ha.mono'
    intro n
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev s).positive n),
      abs_of_pos ((Weight.sobolev ((K : ℝ)*δ)).positive n)]
    exact mul_le_mul_of_nonneg_right (Weight.sobolev_mono hKs n) (norm_nonneg _)
  exact ⟨hmono _ (hall K).1,hmono _ (hall K).2⟩

/-- The original source components have every nonnegative Sobolev
weight at the original exponent; no finite Fourier support is assumed. -/
theorem sourceFiniteGap_mem_all_sobolev
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) (s : ℝ) (hs : 0 ≤ s) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*φ.val.fst n) p ∧
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*φ.val.snd n) p := by
  have h := sourceFiniteGap_physical_mem_sobolev hp hp1 φ hfinite s hs
  have hsample (a : Coeff p)
      (ha : Memℓp (fun n => (Weight.sobolev s n : ℂ)*Coeff.periodDouble a n) p) :
      Memℓp (fun n => (Weight.sobolev s n : ℂ)*a n) p := by
    let b : Coeff p := ⟨_,ha⟩
    apply (Coeff.periodHalve b).property.mono'
    intro n
    change ‖(Weight.sobolev s n : ℂ)*a n‖ ≤
      ‖(Weight.sobolev s (2*n) : ℂ)*Coeff.periodDouble a (2*n)‖
    rw [Coeff.periodDouble_even]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev s).positive n),abs_of_pos ((Weight.sobolev s).positive (2*n))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.rpow_le_rpow (by positivity) _ hs
    simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg (n : ℝ)]
  exact ⟨hsample _ h.1,hsample _ h.2⟩

/-- Every real finite-gap source belongs to `H¹`: both one-derivative
Fourier coefficient sequences are square summable. -/
theorem sourceFiniteGap_mem_H1
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*φ.val.fst n) 2 ∧
    Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*φ.val.snd n) 2 := by
  have h := sourceFiniteGap_mem_all_sobolev hp hp1 φ hfinite 2 (by norm_num)
  have hembed (a : Coeff p) (ha : Memℓp (fun n => (Weight.sobolev 2 n : ℂ)*a n) p) :
      Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*a n) 2 := by
    let b : WeightedCoeff (Weight.sobolev 1) p := ⟨fun n => (Weight.sobolev 1 n : ℂ)*a n, by
      change Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*((Weight.sobolev 1 n : ℂ)*a n)) p
      simpa only [show (2 : ℝ) = 1+1 by norm_num,Weight.sobolev_add,Complex.ofReal_mul,mul_assoc] using ha⟩
    have hb := (WeightedCoeff.sobolevToL1CLM p hp b).property.of_exponent_ge (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
    change Memℓp (fun n => WeightedCoeff.sobolevToL1CLM p hp b n) 2 at hb
    simpa only [WeightedCoeff.sobolevToL1CLM_apply] using hb
  exact ⟨hembed _ h.1,hembed _ h.2⟩

end NLS.ZakharovShabat
