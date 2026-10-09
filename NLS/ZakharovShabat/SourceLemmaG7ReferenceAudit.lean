import NLS.ZakharovShabat.SourceCorollaryG6ReferenceAudit
import NLS.ZakharovShabat.SourceDirichletGradientErrorCotangent
import NLS.ZakharovShabat.SourceFreeDirichletCotangent

/-! # G.7's printed half-wave reference at the actual zero-source gradient

The printed subscripts -2*n*pi introduce an extra pi. The actual free
Dirichlet gradient has subscripts -2*n and coefficient one half.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The corrected half-wave formula, for every signed lattice index. -/
theorem classicalDirichletNormalizedGradient_free_lattice (n : ℤ) (t : Icc (0 : ℝ) 1) :
    classicalDirichletNormalizedGradient 0 ((Real.pi : ℂ)*n) t =
      (1/2 : ℂ) • (wave (2*n) t,wave (-(2*n)) t) := by
  rw [classicalDirichletNormalizedGradient_free]
  apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,wave]
  all_goals
    rw [show (1/2 : ℂ) = (2 : ℂ)⁻¹ by norm_num,div_eq_mul_inv,mul_comm _ (2 : ℂ)⁻¹]
    congr 2; push_cast; ring

/-- Literal first-component error for the actual normalized Dirichlet gradient at zero. -/
def sourceG7PrintedDirichletError (n : ℤ) (t : ℝ) : ℂ :=
  (classicalDirichletNormalizedGradient 0 ((Real.pi : ℂ)*n) t).1-
    sourceG6PrintedWave n t/2

theorem continuous_sourceG7PrintedDirichletError (n : ℤ) :
    Continuous (sourceG7PrintedDirichletError n) := by
  exact ((contDiff_classicalDirichletNormalizedGradient _ _).continuous.fst).sub
    ((continuous_sourceG6PrintedWave n).div_const 2)

theorem sourceG7PrintedDirichletError_eq (n : ℤ) (t : Icc (0 : ℝ) 1) :
    sourceG7PrintedDirichletError n t = (wave (2*n) t-sourceG6PrintedWave n t)/2 := by
  rw [sourceG7PrintedDirichletError,classicalDirichletNormalizedGradient_free_lattice]
  simp only [Prod.smul_fst,smul_eq_mul]
  ring

/-- Actual Fourier coefficients of the printed reference error. -/
def sourceG7PrintedDirichletErrorCoefficients (n : ℤ) : Coeff 2 :=
  unitIntervalL2Coefficients (sourceG7PrintedDirichletError n) (continuous_sourceG7PrintedDirichletError n)

theorem sourceG7PrintedDirichletErrorCoefficients_diagonal (n : ℤ) :
    sourceG7PrintedDirichletErrorCoefficients n n =
      (1-intervalFourierCoefficient 1 (sourceG6PrintedWave n) n)/2 := by
  change intervalFourierCoefficient 1 (sourceG7PrintedDirichletError n) n = _
  rw [intervalFourierCoefficient_congr 1 _
    (fun t => (1/2 : ℂ)*(wave (2*n) t-sourceG6PrintedWave n t))
    (fun t ht => (sourceG7PrintedDirichletError_eq n ⟨t,by simpa using ht⟩).trans (by ring)),
    intervalFourierCoefficient_const_mul,
    intervalFourierCoefficient_sub 1 _ _ (continuous_wave _) (continuous_sourceG6PrintedWave n)]
  have hw : wave (2*n) = unitIntervalExponential ((Real.pi : ℂ)*(2*n : ℤ)) := by
    funext t
    unfold wave unitIntervalExponential
    congr 1
    ring
  rw [hw,intervalFourierCoefficient_exponential_lattice]
  simp
  ring

/-- The literal half-wave error has norm at least one quarter on both signed tails. -/
theorem quarter_le_norm_sourceG7PrintedDirichletErrorCoefficients (n : ℤ) (hn : n ≠ 0) :
    (1/4 : ℝ) ≤ ‖sourceG7PrintedDirichletErrorCoefficients n‖ := by
  have hcoeff := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (sourceG7PrintedDirichletErrorCoefficients n) n
  rw [sourceG7PrintedDirichletErrorCoefficients_diagonal,norm_div,Complex.norm_ofNat] at hcoeff
  have htri := norm_sub_le (1-intervalFourierCoefficient 1 (sourceG6PrintedWave n) n)
    (-intervalFourierCoefficient 1 (sourceG6PrintedWave n) n)
  have hbound := sourceG6PrintedWave_diagonal_le_half n hn
  simp only [sub_neg_eq_add,sub_add_cancel,norm_one,norm_neg] at htri
  linarith

/-- Removing finitely many spectral indices cannot make the printed error summable. -/
theorem not_eventually_sourceG7PrintedError_majorant (b : ℤ → ℝ) (hb : Memℓp b 2) :
    ¬∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs → ‖sourceG7PrintedDirichletErrorCoefficients n‖ ≤ b n := by
  rintro ⟨N,hN⟩
  have hquarter : Memℓp (fun _ : ℤ => (1/4 : ℝ)) 2 := by
    have h := memlp_of_natAbs_eventual_bound 2 (by norm_num) (fun _ : ℤ => (1/4 : ℝ)) b
      (by simpa using hb) (max N 1) (fun n hn => by
        have hn0 : n ≠ 0 := by have := (le_max_right N 1).trans hn; omega
        simpa only [Real.norm_of_nonneg (by norm_num : 0 ≤ (1/4 : ℝ))] using
          (quarter_le_norm_sourceG7PrintedDirichletErrorCoefficients n hn0).trans
            (hN n ((le_max_left N 1).trans hn)))
    simpa using h
  have hs : Summable (fun _ : ℤ => ((1/4 : ℝ)^2)) := by
    simpa using hquarter.summable (by norm_num)
  have hz := (summable_const_iff (β := ℤ) ((1/4 : ℝ)^2)).mp hs
  norm_num at hz

theorem not_memlp_sourceG7PrintedDirichletError_norms :
    ¬Memℓp (fun n : ℤ => ‖sourceG7PrintedDirichletErrorCoefficients n‖) 2 := by
  intro h
  exact not_eventually_sourceG7PrintedError_majorant _ h ⟨0,fun _ _ => le_rfl⟩

/-- The obstruction holds in the exact source pair norm for every second component. -/
theorem not_memlp_sourceG7Printed_pair_norms (c : ℤ → Coeff 2) :
    ¬Memℓp (fun n : ℤ => ‖(CoeffPair.toMax 2).symm
      (Coeff.reflection (sourceG7PrintedDirichletErrorCoefficients n),c n)‖) 2 := by
  intro h
  apply not_memlp_sourceG7PrintedDirichletError_norms
  apply h.mono
  intro n
  have hc := WithLp.norm_fst_le (Coeff 2) ((CoeffPair.toMax 2).symm
    (Coeff.reflection (sourceG7PrintedDirichletErrorCoefficients n),c n))
  simpa using hc

end NLS.ZakharovShabat
