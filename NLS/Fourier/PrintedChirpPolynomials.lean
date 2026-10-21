import NLS.Fourier.ChirpWeightedBlocks

/-! # Uniform bounds for the actual printed Fourier polynomials -/
noncomputable section
set_option autoImplicit false
namespace NLS.Fourier

/-- The actual period-two continuous Fourier term, including the lower cutoff. -/
def printedChirpTerm (n : ℕ) : C(AddCircle (2 : ℝ),ℂ) :=
  printedChirpCoefficient n • fourier (n : ℤ)

/-- Ordinary Fourier cutoffs, with the two prescribed zero terms included. -/
def printedChirpPartialSum (M : ℕ) : C(AddCircle (2 : ℝ),ℂ) :=
  ∑ n ∈ Finset.range M, printedChirpTerm n

/-- The physical evaluation retains the literal logarithmic amplitude and phase. -/
theorem printedChirpTerm_coe (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    printedChirpTerm n (x : AddCircle (2 : ℝ)) =
      (printedChirpAmplitude n : ℂ)*chirpUnit (Real.pi*x) n := by
  simp only [printedChirpTerm,ContinuousMap.coe_smul,Pi.smul_apply,smul_eq_mul,
    printedChirpCoefficient,if_pos (show (2 : ℤ) ≤ n by exact_mod_cast hn),fourier_coe_apply,
    Int.cast_natCast,Complex.ofReal_ofNat,printedChirpAmplitude,chirpUnit,chirpPhase]
  rw [div_mul_eq_mul_div,← Complex.exp_add]
  have he : Complex.I*((n : ℝ)*Real.log n)+2*Real.pi*Complex.I*(n : ℕ)*x/2 =
      ((n : ℝ)*Real.log n+(Real.pi*x)*n : ℝ)*Complex.I := by
    push_cast
    ring
  rw [he]
  push_cast
  ring

/-- A finite suffix is exactly the corresponding block of original terms. -/
theorem printedChirpPartialSum_add_sub (N M : ℕ) :
    printedChirpPartialSum (N+M)-printedChirpPartialSum N =
      ∑ n ∈ Finset.range M, printedChirpTerm (N+n) := by
  rw [printedChirpPartialSum,Finset.sum_range_add,printedChirpPartialSum,add_sub_cancel_left]

/-- A bound in the continuous-function norm for every original dyadic prefix. -/
theorem norm_printedChirpPartialSum_dyadic_prefix (k M : ℕ)
    (hk : 1 ≤ k) (hM : M ≤ 2^k) :
    ‖printedChirpPartialSum (2^k+M)-printedChirpPartialSum (2^k)‖ ≤
      chirpDyadicBoundConstant/(k : ℝ)^(3/2 : ℝ) := by
  rw [printedChirpPartialSum_add_sub]
  apply (ContinuousMap.norm_le _ (div_nonneg chirpDyadicBoundConstant_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg k) _))).mpr
  intro y
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
  have htwo : 2 ≤ 2^k := by
    calc 2 = 2^1 := by norm_num
         _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have he (n : ℕ) : printedChirpTerm (2^k+n) (x : AddCircle (2 : ℝ)) =
      (printedChirpAmplitude ((2 : ℝ)^k+n) : ℂ)*chirpUnit (Real.pi*x) ((2 : ℝ)^k+n) := by
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] using
      printedChirpTerm_coe (2^k+n) (by omega) x
  simpa only [ContinuousMap.sum_apply,he] using
    norm_sum_weighted_chirpUnit_dyadic_le k M (Real.pi*x) hk hM

end NLS.Fourier
