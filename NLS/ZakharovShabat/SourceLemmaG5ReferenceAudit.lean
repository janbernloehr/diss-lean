import NLS.ZakharovShabat.SourceLemmaG3
import NLS.ZakharovShabat.ClassicalEndpointGradientErrorIntegral
import NLS.Fourier.ShiftedExponentialFourier
import NLS.Fourier.IntervalCoefficientLinearity
import NLS.ZakharovShabat.ClassicalGradientInfinityCounterexample
import NLS.SequenceSpaces.PowerDecaySummability

/-! # Audit of the free reference printed in G.5

The two superscripts in the displayed off-diagonal reference are swapped
relative to the actual unconjugated potential gradient and to the proof's
own star-product expansions. Already at zero potential and nu_n=n*pi,
one component of the printed error has Fourier norm one at every index.
Thus even the finite outer p=2 assertion fails with that literal reference.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The lattice terminal phase is exactly the printed (-1)^n, for signed integers. -/
def sourceG5LatticePhase (n : ℤ) : ℂ := cos ((Real.pi : ℂ)*n)

theorem sourceG5LatticePhase_eq (n : ℤ) : sourceG5LatticePhase n = (-1 : ℂ)^n := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (Real.cos_int_mul_pi n)
  simpa only [Complex.ofReal_cos,Complex.ofReal_mul,Complex.ofReal_intCast,
    Complex.ofReal_zpow,Complex.ofReal_neg,Complex.ofReal_one,sourceG5LatticePhase,mul_comm] using h

@[simp] theorem norm_sourceG5LatticePhase (n : ℤ) : ‖sourceG5LatticePhase n‖ = 1 := by
  rw [sourceG5LatticePhase_eq,norm_zpow]
  simp

private theorem sourceG5_free_exponentials (n : ℤ) :
    exp (I*((Real.pi : ℂ)*n)) = sourceG5LatticePhase n ∧
      exp (-I*((Real.pi : ℂ)*n)) = sourceG5LatticePhase n := by
  have hs : sin ((Real.pi : ℂ)*n) = 0 := by rw [mul_comm]; exact sin_int_mul_pi n
  constructor
  · rw [mul_comm,exp_mul_I,hs,zero_mul,add_zero]; rfl
  · rw [show -I*((Real.pi : ℂ)*n) = (-((Real.pi : ℂ)*n))*I by ring,
      exp_mul_I,cos_neg,sin_neg,hs,neg_zero,zero_mul,add_zero]; rfl

private theorem sourceG5_free_wave_squares (n : ℤ) (s : ℝ) :
    exp (I*((Real.pi : ℂ)*n)*s)^2 = wave (2*n) s ∧
      exp (-I*((Real.pi : ℂ)*n)*s)^2 = wave (-(2*n)) s := by
  constructor <;> rw [pow_two,← exp_add] <;> unfold wave <;> congr 1 <;> push_cast <;> ring

/-- The other off-diagonal free gradient, in the same actual derivative convention. -/
theorem classicalFreeEndpointGradient_snd_first (z : ℂ) (s : ℝ) :
    classicalFreeEndpointGradient z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) s =
      (0,-I*exp (I*z)*(exp (-I*z*s))^2) := by
  simp [classicalFreeEndpointGradient,endpointGradientPolynomial,classicalFreeEndpointGradientData,
    classicalFreeVector,pow_two,mul_assoc]

/-- The correct upper reference has its nonzero wave in the minus component. -/
theorem sourceG5_actual_i_free_upper (z : ℂ) (s : ℝ) :
    I • classicalFreeEndpointGradient z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) s =
      (-exp (-I*z)*(exp (I*z*s))^2,0) := by
  rw [classicalFreeEndpointGradient_fst_second]
  ext <;> simp [smul_eq_mul,← mul_assoc]

/-- The correct lower reference has its nonzero wave in the plus component. -/
theorem sourceG5_actual_i_free_lower (z : ℂ) (s : ℝ) :
    I • classicalFreeEndpointGradient z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) s =
      (0,exp (I*z)*(exp (-I*z*s))^2) := by
  rw [classicalFreeEndpointGradient_snd_first]
  ext <;> simp [smul_eq_mul,← mul_assoc]

/-- Actual i times the upper-entry gradient at zero potential and a lattice frequency. -/
theorem sourceG5_actual_i_zero_upper (n : ℤ) (s : Icc (0 : ℝ) 1) :
    I • classicalEndpointGradient 0 ((Real.pi : ℂ)*n) (0,1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) s =
      (-sourceG5LatticePhase n*wave (2*n) s,0) := by
  rw [classicalEndpointGradient_free,sourceG5_actual_i_free_upper,
    (sourceG5_free_exponentials n).2,(sourceG5_free_wave_squares n s).1]

/-- Actual i times the lower-entry gradient at zero potential and a lattice frequency. -/
theorem sourceG5_actual_i_zero_lower (n : ℤ) (s : Icc (0 : ℝ) 1) :
    I • classicalEndpointGradient 0 ((Real.pi : ℂ)*n) (1,0)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) s =
      (0,sourceG5LatticePhase n*wave (-(2*n)) s) := by
  rw [classicalEndpointGradient_free,sourceG5_actual_i_free_lower,
    (sourceG5_free_exponentials n).1,(sourceG5_free_wave_squares n s).2]

/-- The literal upper entry -(-1)^n e^+_(-2n) printed in G.5's second formula. -/
def sourceG5PrintedUpperLattice (n : ℤ) (s : ℝ) : ℂ × ℂ :=
  (0,-sourceG5LatticePhase n*wave (-(2*n)) s)

/-- The literal upper entry of E_z times the reference matrix in G.5's first formula. -/
def sourceG5PrintedUpperReference (z : ℂ) (s : ℝ) : ℂ × ℂ :=
  (0,-exp (-I*z)*(exp (-I*z*s))^2)

/-- At nu_n=n*pi the two printed references agree, including negative n. -/
theorem sourceG5_printed_upper_lattice (n : ℤ) (s : ℝ) :
    sourceG5PrintedUpperReference ((Real.pi : ℂ)*n) s = sourceG5PrintedUpperLattice n s := by
  simp only [sourceG5PrintedUpperReference,sourceG5PrintedUpperLattice,
    (sourceG5_free_exponentials n).2,(sourceG5_free_wave_squares n s).2]

/-- A scalar component of the actual gradient minus the literal printed reference. -/
def sourceG5PrintedUpperError (n : ℤ) (s : ℝ) : ℂ :=
  ((I • classicalEndpointGradient 0 ((Real.pi : ℂ)*n) (0,1)
    (ContinuousLinearMap.fst ℂ ℂ ℂ) s)-sourceG5PrintedUpperLattice n s).1

theorem continuous_sourceG5PrintedUpperError (n : ℤ) : Continuous (sourceG5PrintedUpperError n) := by
  have hc := continuous_classicalEndpointGradient 0 ((Real.pi : ℂ)*n) (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ)
  change Continuous (fun s => I * (classicalEndpointGradient 0 ((Real.pi : ℂ)*n)
    (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) s).1 - 0)
  simpa only [sub_zero] using hc.fst.const_mul I

theorem sourceG5PrintedUpperError_eq (n : ℤ) (s : Icc (0 : ℝ) 1) :
    sourceG5PrintedUpperError n s = -sourceG5LatticePhase n*wave (2*n) s := by
  simp only [sourceG5PrintedUpperError,sourceG5_actual_i_zero_upper,sourceG5PrintedUpperLattice,
    Prod.fst_sub,sub_zero]

/-- These are the actual Fourier integrals of that component of the printed error. -/
def sourceG5PrintedUpperErrorCoefficients (n : ℤ) : Coeff 2 :=
  unitIntervalL2Coefficients (sourceG5PrintedUpperError n) (continuous_sourceG5PrintedUpperError n)

/-- The moving Fourier coefficient has modulus one; there is no spectral-index decay. -/
theorem sourceG5PrintedUpperErrorCoefficients_diagonal (n : ℤ) :
    sourceG5PrintedUpperErrorCoefficients n n = -sourceG5LatticePhase n := by
  change intervalFourierCoefficient 1 (sourceG5PrintedUpperError n) n = _
  rw [intervalFourierCoefficient_congr 1 _ (fun s => -sourceG5LatticePhase n*wave (2*n) s)
    (fun s hs => sourceG5PrintedUpperError_eq n ⟨s,by simpa using hs⟩),
    intervalFourierCoefficient_const_mul]
  have hw : wave (2*n) = unitIntervalExponential ((Real.pi : ℂ)*(2*n : ℤ)) := by
    funext s
    unfold wave unitIntervalExponential
    congr 1
    ring
  rw [hw,intervalFourierCoefficient_exponential_lattice]
  simp

theorem one_le_norm_sourceG5PrintedUpperErrorCoefficients (n : ℤ) :
    1 ≤ ‖sourceG5PrintedUpperErrorCoefficients n‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (sourceG5PrintedUpperErrorCoefficients n) n
  simpa only [sourceG5PrintedUpperErrorCoefficients_diagonal,norm_neg,norm_sourceG5LatticePhase] using h

/-- The literal printed reference fails already at the finite endpoint p=2.
This is a component of the full matrix error, not a different reference solution. -/
theorem not_memlp_sourceG5PrintedUpperError_norms :
    ¬Memℓp (fun n : ℤ => ‖sourceG5PrintedUpperErrorCoefficients n‖) 2 := by
  intro h
  have h1 : Memℓp (fun _ : ℤ => (1 : ℝ)) 2 := h.mono (fun n => by
    simpa only [norm_one] using one_le_norm_sourceG5PrintedUpperErrorCoefficients n)
  have hs : Summable (fun _ : ℤ => (1 : ℝ)) := by simpa using h1.summable (by norm_num)
  exact one_ne_zero ((summable_const_iff (β := ℤ) (1 : ℝ)).mp hs)

/-- Consequently no matrix norm majorizing this component can have the claimed ℓ² property. -/
theorem not_memlp_sourceG5PrintedError_majorant (b : ℤ → ℝ)
    (hb : ∀ n, ‖sourceG5PrintedUpperErrorCoefficients n‖ ≤ b n) : ¬Memℓp b 2 := by
  intro h
  apply not_memlp_sourceG5PrintedUpperError_norms
  exact h.mono (fun n => by simpa only [norm_norm] using hb n)

/-- Discarding any finite initial spectral segment cannot repair the printed estimate. -/
theorem not_eventually_sourceG5PrintedError_majorant (b : ℤ → ℝ) (hb : Memℓp b 2) :
    ¬∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
      ‖sourceG5PrintedUpperErrorCoefficients n‖ ≤ b n := by
  rintro ⟨N,hN⟩
  apply not_memlp_sourceG5PrintedUpperError_norms
  have h := memlp_of_natAbs_eventual_bound 2 (by norm_num)
    (fun n => ‖sourceG5PrintedUpperErrorCoefficients n‖) b (by simpa using hb) N
    (fun n hn => by simpa only [norm_norm] using hN n hn)
  simpa using h

/-- The counterexample is the original zero H¹ source, with both frequency hypotheses exact. -/
theorem sourceG5_zero_admissible :
    classicalSobolevPotential (sourceG3ClassicalCoefficients (0,0)) = 0 ∧
      (∀ n : ℤ, ‖((Real.pi : ℂ)*n)-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) ∧
      (∀ n : ℤ, ‖((Real.pi : ℂ)*n)-(Real.pi : ℂ)*n‖ ≤ 0/(n.natAbs : ℝ)) := by
  have hz : sourceG3ClassicalCoefficients (0,0) = 0 := by
    change (Coeff.periodDoubleSobolevCLM 0,Coeff.periodDoubleSobolevCLM 0) = 0
    simp
  refine ⟨?_,fun n => ?_,fun n => ?_⟩
  · rw [hz]
    ext t <;> simp [classicalSobolevPotential,sobolevUnitCurve]
  · simp only [sub_self,norm_zero]; positivity
  · simp

/-- The independent infinity-endpoint counterexample is also an original period-one H¹ source. -/
theorem sourceG5_triangular_coefficients :
    sourceG3ClassicalCoefficients triangularSobolevCoefficients = triangularSobolevCoefficients := by
  simp only [sourceG3ClassicalCoefficients,triangularSobolevCoefficients,
    Coeff.periodDoubleSobolev_scalarMode,mul_zero]
  congr 1
  exact Coeff.periodDoubleSobolevCLM.map_zero

/-- Even after correcting the off-diagonal reference, the printed p=infinity endpoint fails.
This diagonal component has zero free reference for both formulas. -/
theorem sourceG5_not_eventually_fourier_l1 (ω : ℤ → ℂ) :
    ¬∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
      Memℓp (intervalFourierCoefficient 1 (fun t =>
        (classicalEndpointGradientRemainder
          (classicalSobolevPotential (sourceG3ClassicalCoefficients triangularSobolevCoefficients))
          (gradientCounterexampleFrequency n) (ω n) (1,0)
          (ContinuousLinearMap.fst ℂ ℂ ℂ) t).2)) 1 := by
  rw [sourceG5_triangular_coefficients]
  exact not_eventually_memlp_gradientCounterexampleFrequency_one ω

end NLS.ZakharovShabat
