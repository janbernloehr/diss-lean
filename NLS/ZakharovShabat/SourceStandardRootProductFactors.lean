import NLS.ZakharovShabat.SourceStandardRootAlgebra

/-!
# Paired factors for the standard-root product

Lemma 10.5 normalizes each noncentral standard root by its free value
`π k`. Pairing the factors at `k` and `-k` cancels their nonsummable
spectral-parameter terms. These identities isolate the midpoint and
square-root errors used in the subsequent product convergence argument.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The deviation of one normalized standard root from its free factor. -/
def standardRootRelativeError (t g d z : ℂ) : ℂ :=
  normalizedStandardRoot t g z / d - 1

/-- The principal square root has a global one-sided Lipschitz bound
at `1`. This controls the radicand error in each product factor. -/
theorem norm_sqrt_sub_one_le (w : ℂ) :
    ‖Complex.sqrt w - 1‖ ≤ ‖w - 1‖ := by
  have hre : 0 ≤ (Complex.sqrt w).re := by
    rw [Complex.sqrt, Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hden : 1 ≤ ‖Complex.sqrt w + 1‖ := by
    calc
      1 ≤ (Complex.sqrt w + 1).re := by simp [hre]
      _ ≤ ‖Complex.sqrt w + 1‖ := Complex.re_le_norm _
  have hsqrt : Complex.sqrt w ^ 2 = w := by
    have h := Complex.cpow_nat_inv_pow w (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt, one_div] using h
  have hprod : (Complex.sqrt w - 1) * (Complex.sqrt w + 1) = w - 1 := by
    calc
      _ = Complex.sqrt w ^ 2 - 1 := by ring
      _ = w - 1 := by rw [hsqrt]
  rw [← hprod, norm_mul]
  have hn : 0 ≤ ‖Complex.sqrt w - 1‖ := norm_nonneg _
  nlinarith

theorem norm_sqrt_one_sub_sub_one_le (q : ℂ) :
    ‖Complex.sqrt (1-q) - 1‖ ≤ ‖q‖ := by
  simpa only [sub_sub_cancel_left, norm_neg] using norm_sqrt_sub_one_le (1-q)

/-- The exact three-term decomposition in the proof of Lemma 10.5. -/
theorem standardRootRelativeError_eq (t g d z : ℂ) (hd : d ≠ 0) :
    standardRootRelativeError t g d z =
      (t-d)/d - z/d +
        (t-z)/d * (Complex.sqrt (1-g/(4*(t-z)^2))-1) := by
  unfold standardRootRelativeError normalizedStandardRoot
  field_simp
  ring

/-- A pointwise factor estimate in terms of midpoint displacement and
the squared-gap radicand. -/
theorem norm_standardRootRelativeError_le (t g d z : ℂ) (hd : d ≠ 0) :
    ‖standardRootRelativeError t g d z‖ ≤
      ‖t-d‖ / ‖d‖ + ‖z‖ / ‖d‖ +
        (‖t-z‖ / ‖d‖) * ‖g / (4*(t-z)^2)‖ := by
  rw [standardRootRelativeError_eq t g d z hd]
  calc
    _ ≤ ‖(t-d)/d‖ + ‖z/d‖ +
        ‖(t-z)/d * (Complex.sqrt (1-g/(4*(t-z)^2))-1)‖ := by
          calc
            _ ≤ ‖(t-d)/d - z/d‖ +
                ‖(t-z)/d * (Complex.sqrt (1-g/(4*(t-z)^2))-1)‖ :=
              norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_div, norm_div, norm_mul, norm_div]
      gcongr
      exact norm_sqrt_one_sub_sub_one_le _

/-- The `z/d` and `z/(-d)` terms cancel in a paired error. -/
theorem standardRootRelativeError_pair (tpos tneg gpos gneg d z : ℂ)
    (hd : d ≠ 0) :
    standardRootRelativeError tpos gpos d z +
        standardRootRelativeError tneg gneg (-d) z =
      (tpos-d)/d + (tneg+d)/(-d) +
        (tpos-z)/d * (Complex.sqrt (1-gpos/(4*(tpos-z)^2))-1) +
        (tneg-z)/(-d) * (Complex.sqrt (1-gneg/(4*(tneg-z)^2))-1) := by
  rw [standardRootRelativeError_eq _ _ _ _ hd,
    standardRootRelativeError_eq _ _ _ _ (neg_ne_zero.mpr hd)]
  have hc : z / -d = -(z/d) := by ring
  rw [hc]
  ring

/-- The product of the two normalized roots is expressed through their
individual errors. This is the paired factor `1+a_k+a_{-k}+a_ka_{-k}`. -/
theorem standardRootRelativeError_pair_factor (tpos tneg gpos gneg d z : ℂ) :
    (normalizedStandardRoot tpos gpos z / d) *
        (normalizedStandardRoot tneg gneg z / (-d)) =
      1 + standardRootRelativeError tpos gpos d z +
        standardRootRelativeError tneg gneg (-d) z +
        standardRootRelativeError tpos gpos d z *
          standardRootRelativeError tneg gneg (-d) z := by
  unfold standardRootRelativeError
  ring

/-- Source-specific normalized factor error at a nonzero index. -/
def sourceStandardRootRelativeError (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (k : ℤ) (z : ℂ) : ℂ :=
  sourceStandardRoot hp hp1 ψ k z / ((Real.pi : ℂ)*k) - 1

/-- The source factor error separates midpoint displacement, spectral
parameter, and square-root error. -/
theorem sourceStandardRootRelativeError_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (k : ℤ) (z : ℂ) (hk : k ≠ 0) :
    sourceStandardRootRelativeError hp hp1 ψ k z =
      sourcePeriodicMidpointDisplacement hp hp1 ψ k / ((Real.pi : ℂ)*k) -
        z / ((Real.pi : ℂ)*k) +
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) k-z) / ((Real.pi : ℂ)*k) *
          (Complex.sqrt (1-
            (canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) k)^2 /
              (4*(canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) k-z)^2))-1) := by
  have hd : (Real.pi : ℂ)*k ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast hk)
  change standardRootRelativeError
    (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) k)
    ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) k)^2) ((Real.pi : ℂ)*k) z = _
  rw [standardRootRelativeError_eq _ _ _ _ hd]
  rw [sourcePeriodicMidpointDisplacement_apply]

/-- For opposite nonzero indices, the free spectral terms cancel. -/
theorem sourceStandardRootRelativeError_pair (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (k : ℤ) (z : ℂ) (hk : k ≠ 0) :
    sourceStandardRootRelativeError hp hp1 ψ k z +
        sourceStandardRootRelativeError hp hp1 ψ (-k) z =
      sourcePeriodicMidpointDisplacement hp hp1 ψ k / ((Real.pi : ℂ)*k) +
        sourcePeriodicMidpointDisplacement hp hp1 ψ (-k) /
          (-((Real.pi : ℂ)*k)) +
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) k-z) / ((Real.pi : ℂ)*k) *
          (Complex.sqrt (1-
            (canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) k)^2 /
              (4*(canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) k-z)^2))-1) +
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) (-k)-z) / (-((Real.pi : ℂ)*k)) *
          (Complex.sqrt (1-
            (canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) (-k))^2 /
              (4*(canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) (-k)-z)^2))-1) := by
  rw [sourceStandardRootRelativeError_eq hp hp1 ψ k z hk,
    sourceStandardRootRelativeError_eq hp hp1 ψ (-k) z (neg_ne_zero.mpr hk)]
  norm_num only [Int.cast_neg]
  ring

/-- The source paired product has the exact `1+a_k+a_{-k}+a_ka_{-k}`
form from Lemma 10.5. -/
theorem sourceStandardRoot_pair_factor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (k : ℤ) (z : ℂ) :
    (sourceStandardRoot hp hp1 ψ k z / ((Real.pi : ℂ)*k)) *
      (sourceStandardRoot hp hp1 ψ (-k) z / (-((Real.pi : ℂ)*k))) =
      1 + sourceStandardRootRelativeError hp hp1 ψ k z +
        sourceStandardRootRelativeError hp hp1 ψ (-k) z +
        sourceStandardRootRelativeError hp hp1 ψ k z *
          sourceStandardRootRelativeError hp hp1 ψ (-k) z := by
  unfold sourceStandardRootRelativeError
  simp only [Int.cast_neg, mul_neg]
  ring

end NLS.ZakharovShabat
