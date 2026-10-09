import NLS.ZakharovShabat.SourceLemmaG5
import NLS.Fourier.RealExponentialCoefficientBound

/-! # The extra pi in the wave subscripts printed in G.6

With e_alpha(x)=exp(i*pi*alpha*x), the printed subscript -2*n*pi
introduces pi twice. The actual zero-source anti-discriminant gradient
has waves with subscripts -2*n. The literal error is not outer l2.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The first-component wave in the reference literally printed on page 138. -/
def sourceG6PrintedWave (n : ℤ) : ℝ → ℂ :=
  unitIntervalExponential ((2*Real.pi^2*(n : ℝ) : ℝ) : ℂ)

theorem continuous_sourceG6PrintedWave (n : ℤ) : Continuous (sourceG6PrintedWave n) :=
  (contDiff_unitIntervalExponential _).continuous

/-- Literal (-1)^n (e^+_(-2*n*pi)-e^-_(-2*n*pi)). -/
def sourceG6PrintedReference (n : ℤ) (s : ℝ) : ℂ × ℂ :=
  sourceG5LatticePhase n • (-sourceG6PrintedWave n s,sourceG6PrintedWave (-n) s)

/-- First component of i times the actual zero-source gradient minus the printed reference. -/
def sourceG6PrintedAntiError (n : ℤ) (s : ℝ) : ℂ :=
  (I • classicalAntiDiscriminantGradient 0 ((Real.pi : ℂ)*n) s-sourceG6PrintedReference n s).1

theorem continuous_sourceG6PrintedAntiError (n : ℤ) : Continuous (sourceG6PrintedAntiError n) := by
  change Continuous (fun s => I*(classicalAntiDiscriminantGradient 0 ((Real.pi : ℂ)*n) s).1-
    sourceG5LatticePhase n*(-sourceG6PrintedWave n s))
  exact ((continuous_classicalAntiDiscriminantGradient _ _).fst.const_mul I).sub
    (((contDiff_unitIntervalExponential _).continuous.neg).const_mul _)

theorem sourceG6PrintedAntiError_eq (n : ℤ) (s : Icc (0 : ℝ) 1) :
    sourceG6PrintedAntiError n s =
      sourceG5LatticePhase n*(sourceG6PrintedWave n s-wave (2*n) s) := by
  simp only [sourceG6PrintedAntiError,sourceG6PrintedReference,
    classicalAntiDiscriminantGradient_free_lattice n s s.property,
    Prod.fst_sub,Prod.smul_fst,smul_eq_mul]
  change I*(I*sourceG5LatticePhase n*wave (2*n) s)-
    sourceG5LatticePhase n*(-sourceG6PrintedWave n s) = _
  ring_nf
  simp [I_sq]

/-- Actual unit-interval Fourier coefficients, including their Hilbert norm. -/
def sourceG6PrintedAntiErrorCoefficients (n : ℤ) : Coeff 2 :=
  unitIntervalL2Coefficients (sourceG6PrintedAntiError n) (continuous_sourceG6PrintedAntiError n)

theorem sourceG6PrintedAntiErrorCoefficients_diagonal (n : ℤ) :
    sourceG6PrintedAntiErrorCoefficients n n = sourceG5LatticePhase n*
      (intervalFourierCoefficient 1 (sourceG6PrintedWave n) n-1) := by
  change intervalFourierCoefficient 1 (sourceG6PrintedAntiError n) n = _
  rw [intervalFourierCoefficient_congr 1 _
    (fun s => sourceG5LatticePhase n*(sourceG6PrintedWave n s-wave (2*n) s))
    (fun s hs => sourceG6PrintedAntiError_eq n ⟨s,by simpa using hs⟩),
    intervalFourierCoefficient_const_mul,
    intervalFourierCoefficient_sub 1 (sourceG6PrintedWave n) (wave (2*n))
      (continuous_sourceG6PrintedWave n) (continuous_wave _)]
  have hw : wave (2*n) = unitIntervalExponential ((Real.pi : ℂ)*(2*n : ℤ)) := by
    funext s
    unfold wave unitIntervalExponential
    congr 1
    ring
  rw [hw,intervalFourierCoefficient_exponential_lattice]
  simp

/-- The printed wave has Fourier overlap at most one half with the correct moving mode. -/
theorem sourceG6PrintedWave_diagonal_le_half (n : ℤ) (hn : n ≠ 0) :
    ‖intervalFourierCoefficient 1 (sourceG6PrintedWave n) n‖ ≤ (1/2 : ℝ) := by
  have hn1 : 1 ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn
  have hpi := Real.pi_gt_three
  have hpi1 : 0 < Real.pi-1 := by linarith
  have hd : 4 ≤ |2*Real.pi^2*(n : ℝ)-2*Real.pi*n| := by
    rw [show 2*Real.pi^2*(n : ℝ)-2*Real.pi*n = 2*Real.pi*(Real.pi-1)*n by ring,
      abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi*(Real.pi-1))]
    have h := mul_le_mul_of_nonneg_left hn1 (by positivity : 0 ≤ 2*Real.pi*(Real.pi-1))
    nlinarith
  have hz : 2*Real.pi^2*(n : ℝ)-2*Real.pi*n ≠ 0 := by
    intro he
    rw [he,abs_zero] at hd
    norm_num at hd
  exact (norm_intervalFourierCoefficient_exponential_real_le _ n hz).trans
    ((div_le_iff₀ (by linarith : 0 < |2*Real.pi^2*(n : ℝ)-2*Real.pi*n|)).mpr (by linarith))

/-- The literal reference error does not decay along either signed spectral tail. -/
theorem half_le_norm_sourceG6PrintedAntiErrorCoefficients (n : ℤ) (hn : n ≠ 0) :
    (1/2 : ℝ) ≤ ‖sourceG6PrintedAntiErrorCoefficients n‖ := by
  have hcoeff := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (sourceG6PrintedAntiErrorCoefficients n) n
  rw [sourceG6PrintedAntiErrorCoefficients_diagonal,norm_mul,norm_sourceG5LatticePhase,one_mul] at hcoeff
  have htri := norm_sub_le (intervalFourierCoefficient 1 (sourceG6PrintedWave n) n)
    (intervalFourierCoefficient 1 (sourceG6PrintedWave n) n-1)
  have hbound := sourceG6PrintedWave_diagonal_le_half n hn
  simp only [sub_sub_cancel,norm_one] at htri
  linarith

/-- A finite exceptional set cannot repair G.6 with the literal printed wave frequency. -/
theorem not_eventually_sourceG6PrintedError_majorant (b : ℤ → ℝ) (hb : Memℓp b 2) :
    ¬∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs → ‖sourceG6PrintedAntiErrorCoefficients n‖ ≤ b n := by
  rintro ⟨N,hN⟩
  have hhalf : Memℓp (fun _ : ℤ => (1/2 : ℝ)) 2 := by
    have h := memlp_of_natAbs_eventual_bound 2 (by norm_num) (fun _ : ℤ => (1/2 : ℝ)) b
      (by simpa using hb) (max N 1) (fun n hn => by
        have hn0 : n ≠ 0 := by have := (le_max_right N 1).trans hn; omega
        simpa only [Real.norm_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ))] using
          (half_le_norm_sourceG6PrintedAntiErrorCoefficients n hn0).trans (hN n ((le_max_left N 1).trans hn)))
    simpa using h
  have hs : Summable (fun _ : ℤ => ((1/2 : ℝ)^2)) := by
    simpa using hhalf.summable (by norm_num)
  have hz := (summable_const_iff (β := ℤ) ((1/2 : ℝ)^2)).mp hs
  norm_num at hz

theorem not_memlp_sourceG6PrintedAntiError_norms :
    ¬Memℓp (fun n : ℤ => ‖sourceG6PrintedAntiErrorCoefficients n‖) 2 := by
  intro h
  exact not_eventually_sourceG6PrintedError_majorant _ h ⟨0,fun _ _ => le_rfl⟩

end NLS.ZakharovShabat
