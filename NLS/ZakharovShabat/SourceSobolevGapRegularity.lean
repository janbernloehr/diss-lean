import NLS.ZakharovShabat.SourceGapWeightedRegularity
import NLS.ZakharovShabat.SourceSection14WeightedMembership

/-! # Exact original source regularity from Sobolev gaps

Half-scale spectral weights preserve the original Fourier convention.
Finite iteration divides the requested order into small gains and reaches
that exact order without assuming any greater gap regularity.
-/

noncomputable section

namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Lift a real source from order t to t+s using gaps of order t+s,
for a positive gain s below the algebraic remainder threshold. -/
theorem source_mem_sobolev_step_of_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (t s : ℝ) (ht : 0 ≤ t) (hs : 0 < s) (hsp : s*p.toReal < min 1 (p.toReal-1))
    (hφ : Memℓp (fun n => (Weight.sobolev t n:ℂ)*φ.val.fst n) p ∧
      Memℓp (fun n => (Weight.sobolev t n:ℂ)*φ.val.snd n) p)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev (t+s) n:ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n) p) :
    Memℓp (fun n => (Weight.sobolev (t+s) n:ℂ)*φ.val.fst n) p ∧
    Memℓp (fun n => (Weight.sobolev (t+s) n:ℂ)*φ.val.snd n) p := by
  let w := sourceSobolevSpectralWeight t ht
  let a : CoeffPair p := WithLp.toLp p (⟨_,hφ.1⟩,⟨_,hφ.2⟩)
  let ψ := normalizedWeightedPeriodOne w a
  have he : normalizedWeightedSource w a = φ.val := by
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext n
    · change (normalizedWeightedSource w a).fst n = φ.val.fst n
      rw [normalizedWeightedSource_fst]
      change ((Weight.sobolev t n:ℂ)*φ.val.fst n)/(w (2*n):ℂ) = _
      rw [show w (2*n) = Weight.sobolev t n from sourceSobolevSpectralWeight_even t ht n]
      exact mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev t) n)
    · change (normalizedWeightedSource w a).snd n = φ.val.snd n
      rw [normalizedWeightedSource_snd]
      change ((Weight.sobolev t n:ℂ)*φ.val.snd n)/(w (2*n):ℂ) = _
      rw [show w (2*n) = Weight.sobolev t n from sourceSobolevSpectralWeight_even t ht n]
      exact mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev t) n)
  have hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val := by
    dsimp only [ψ]
    rw [forget_normalizedWeightedPeriodOne,he]
  have hgap' : Memℓp (fun n : ℤ => (Weight.sobolev s n:ℂ)*
      ((w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n)) p := by
    simp only [w,sourceSobolevSpectralWeight_even]
    simpa only [Weight.sobolev_add,Complex.ofReal_mul,
      mul_assoc,mul_left_comm,mul_comm] using hgap
  have hg := source_weighted_mem_sobolev_of_gap hp hp1 φ w ψ hψ s hs hsp hgap'
  have hsample (a₀ : Coeff p) (b : WeightedCoeff w.toWeight p)
      (hraw : ∀ n : ℤ, b.val (2*n) = a₀ n)
      (hb : Memℓp (fun n : ℤ => (Weight.sobolev s n:ℂ)*((w n:ℂ)*b.val n)) p) :
      Memℓp (fun n : ℤ => (Weight.sobolev (t+s) n:ℂ)*a₀ n) p := by
    let c : Coeff p := ⟨_,hb⟩
    apply (Coeff.periodHalve c).property.mono'
    intro n
    change ‖(Weight.sobolev (t+s) n:ℂ)*a₀ n‖ ≤
      ‖(Weight.sobolev s (2*n):ℂ)*((w (2*n):ℂ)*b.val (2*n))‖
    rw [hraw n,show w (2*n) = Weight.sobolev t n from sourceSobolevSpectralWeight_even t ht n]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev s).positive n),abs_of_pos ((Weight.sobolev s).positive (2*n)),
      abs_of_pos ((Weight.sobolev t).positive n),Weight.sobolev_add]
    have hweight : Weight.sobolev s n ≤ Weight.sobolev s (2*n) := by
      apply Real.rpow_le_rpow (by positivity) _ hs.le
      simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith [abs_nonneg (n:ℝ)]
    have h := mul_le_mul_of_nonneg_right hweight
      (mul_nonneg ((Weight.sobolev t).positive n).le (norm_nonneg (a₀ n)))
    simpa only [mul_assoc,mul_left_comm] using h
  constructor
  · apply hsample φ.val.fst ψ.fst _ hg.1
    intro n
    have h := congrArg (fun b : WeightedCoeffPair SpectralWeight.one.toWeight p => b.fst.val (2*n)) hψ
    simpa using h
  · apply hsample φ.val.snd ψ.snd _ hg.2
    intro n
    have h := congrArg (fun b : WeightedCoeffPair SpectralWeight.one.toWeight p => b.snd.val (2*n)) hψ
    simpa using h
end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Weighted actual gaps imply the same exact nonnegative Sobolev order
on both original source components, at every finite p>1. -/
theorem source_mem_sobolev_of_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (s : ℝ) (hs : 0 ≤ s)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev s n:ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n) p) :
    Memℓp (fun n => (Weight.sobolev s n:ℂ)*φ.val.fst n) p ∧
    Memℓp (fun n => (Weight.sobolev s n:ℂ)*φ.val.snd n) p := by
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · subst s
    simpa only [Weight.sobolev_zero_apply,Complex.ofReal_one,one_mul] using
      (show Memℓp (fun n => φ.val.fst n) p ∧ Memℓp (fun n => φ.val.snd n) p from
        ⟨φ.val.fst.property,φ.val.snd.property⟩)
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hp0 : 0 < p.toReal := zero_lt_one.trans hpR
  let α := min 1 (p.toReal-1)
  have hα : 0 < α := lt_min (by norm_num) (by linarith)
  obtain ⟨K,hK⟩ := exists_nat_gt (s*p.toReal/α)
  have hKr : 0 < (K:ℝ) := (div_pos (mul_pos hs0 hp0) hα).trans hK
  let δ := s/(K:ℝ)
  have hδ : 0 < δ := div_pos hs0 hKr
  have hδp : δ*p.toReal < min 1 (p.toReal-1) := by
    have he : δ*p.toReal = (s*p.toReal)/(K:ℝ) := by dsimp [δ]; ring
    rw [he]
    exact (div_lt_iff₀ hKr).mpr (by have h := (div_lt_iff₀ hα).mp hK; nlinarith)
  have hKδ : (K:ℝ)*δ = s := by dsimp [δ]; field_simp
  have hall (k : ℕ) (hk : k ≤ K) :
      Memℓp (fun n => (Weight.sobolev ((k:ℝ)*δ) n:ℂ)*φ.val.fst n) p ∧
      Memℓp (fun n => (Weight.sobolev ((k:ℝ)*δ) n:ℂ)*φ.val.snd n) p := by
    induction k with
    | zero =>
      simpa only [Nat.cast_zero,zero_mul,Weight.sobolev_zero_apply,Complex.ofReal_one,one_mul] using
        (show Memℓp (fun n => φ.val.fst n) p ∧ Memℓp (fun n => φ.val.snd n) p from
          ⟨φ.val.fst.property,φ.val.snd.property⟩)
    | succ k ih =>
      have hle : (k:ℝ)*δ+δ ≤ s := by
        have hkr : (k:ℝ)+1 ≤ K := by exact_mod_cast hk
        have h := mul_le_mul_of_nonneg_right hkr hδ.le
        rw [hKδ] at h
        nlinarith
      have hg : Memℓp (fun n : ℤ => (Weight.sobolev ((k:ℝ)*δ+δ) n:ℂ)*
          sourcePeriodicGapDisplacement hp hp1 φ.val n) p := by
        apply hgap.mono'
        intro n
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos ((Weight.sobolev ((k:ℝ)*δ+δ)).positive n),
          abs_of_pos ((Weight.sobolev s).positive n)]
        exact mul_le_mul_of_nonneg_right (Weight.sobolev_mono hle n) (norm_nonneg _)
      have h := source_mem_sobolev_step_of_gap hp hp1 φ ((k:ℝ)*δ) δ
        (by positivity) hδ hδp (ih (by omega)) hg
      simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using h
  simpa only [hKδ] using hall K le_rfl
end NLS.ZakharovShabat
