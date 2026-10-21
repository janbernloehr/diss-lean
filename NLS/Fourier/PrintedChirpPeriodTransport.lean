import NLS.Fourier.PrintedChirpLiteralSeries
import NLS.Fourier.CircleHausdorffYoungSynthesis

/-! # Explicit physical-period transport of the printed chirp -/
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped ENNReal
namespace NLS.Fourier
variable (L : ℝ) [Fact (0 < L)]

/-- Pull back from the period-two circle with the physical coordinate rescaling visible. -/
def chirpPeriodPullback : C(AddCircle (2 : ℝ),ℂ) →L[ℂ] C(AddCircle L,ℂ) :=
  ContinuousMap.compCLM ℂ ℂ
    ⟨AddCircle.homeomorphAddCircle L 2 (ne_of_gt (Fact.out : 0 < L)) (by norm_num),
      (AddCircle.homeomorphAddCircle L 2 (ne_of_gt (Fact.out : 0 < L)) (by norm_num)).continuous⟩

/-- The rescaled displayed witness at an arbitrary positive physical period. -/
def printedChirpAtPeriod : C(AddCircle L,ℂ) := chirpPeriodPullback L printedChirpContinuous

theorem printedChirpAtPeriod_coe (x : ℝ) :
    printedChirpAtPeriod L (x : AddCircle L) = printedChirpFunction (2*x/L) := by
  change printedChirpContinuous ((x*(L⁻¹*2) : ℝ) : AddCircle (2 : ℝ)) = _
  rw [show x*(L⁻¹*2) = 2*x/L by ring]
  rfl

/-- Every Fourier character retains its signed integer mode under physical rescaling. -/
theorem chirpPeriodPullback_fourier (n : ℤ) :
    chirpPeriodPullback L (fourier n) = fourier n := by
  ext y
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
  change fourier n (((x*(L⁻¹*2) : ℝ)) : AddCircle (2 : ℝ)) =
    (fourier n : C(AddCircle L,ℂ)) (x : AddCircle L)
  rw [fourier_coe_apply,fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- The rescaled continuous sum is the limit of the same coefficients in the new physical basis. -/
theorem tendsto_printedChirpAtPeriod :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
      printedChirpCoefficient n • (fourier (n : ℤ) : C(AddCircle L,ℂ)))
      atTop (𝓝 (printedChirpAtPeriod L)) := by
  have h := (chirpPeriodPullback L).continuous.tendsto printedChirpContinuous |>.comp
    tendsto_printedChirpPartialSum
  simpa only [printedChirpAtPeriod,printedChirpPartialSum,map_sum,printedChirpTerm,
    map_smul,chirpPeriodPullback_fourier,Function.comp_def] using h

private def chirpPeriodCoefficient (m : ℤ) : C(AddCircle L,ℂ) →L[ℂ] ℂ :=
  (circleLpCoefficient (L := L) (q := 1) m).comp
    (ContinuousMap.toLp (E := ℂ) 1 (AddCircle.haarAddCircle (T := L)) ℂ)

private theorem chirpPeriodCoefficient_apply (m : ℤ) (f : C(AddCircle L,ℂ)) :
    chirpPeriodCoefficient L m f = fourierCoeff f m := by
  change fourierCoeff (ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ f) m = _
  rw [fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _)]

/-- Physical rescaling preserves every actual signed Fourier coefficient of this witness. -/
theorem fourierCoeff_printedChirpAtPeriod (m : ℤ) :
    fourierCoeff (printedChirpAtPeriod L) m = printedChirpCoefficient m := by
  have hL := (chirpPeriodCoefficient L m).continuous.tendsto (printedChirpAtPeriod L) |>.comp
    (tendsto_printedChirpAtPeriod L)
  have h2 := (chirpPeriodCoefficient 2 m).continuous.tendsto printedChirpContinuous |>.comp
    tendsto_printedChirpPartialSum
  have he (M : ℕ) :
      chirpPeriodCoefficient L m (∑ n ∈ Finset.range M,
        printedChirpCoefficient n • (fourier (n : ℤ) : C(AddCircle L,ℂ))) =
      chirpPeriodCoefficient 2 m (printedChirpPartialSum M) := by
    simp only [printedChirpPartialSum,printedChirpTerm,map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro n _
    rw [chirpPeriodCoefficient_apply,chirpPeriodCoefficient_apply,
      fourierCoeff_fourier,fourierCoeff_fourier]
  have hL' : Tendsto (fun M => chirpPeriodCoefficient 2 m (printedChirpPartialSum M))
      atTop (𝓝 (chirpPeriodCoefficient L m (printedChirpAtPeriod L))) := by
    simpa only [Function.comp_def,he] using hL
  have hh := tendsto_nhds_unique hL' h2
  simpa only [chirpPeriodCoefficient_apply,fourierCoeff_printedChirpContinuous] using hh

/-- The same explicit witness has the original Fourier-Lebesgue threshold at every positive period. -/
theorem printedChirpAtPeriod_mem_original_iff {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    SmoothPeriodicTest.Distribution.ofContinuous (printedChirpAtPeriod L) ∈
      periodicFourierLebesgueSubmodule Weight.one p ↔ 2 ≤ p := by
  change Memℓp (fun k => (Weight.one k : ℂ)*
    SmoothPeriodicTest.Distribution.ofContinuous (printedChirpAtPeriod L)
      (SmoothPeriodicTest.mode (-k))) p ↔ 2 ≤ p
  simp only [Weight.one_apply,Complex.ofReal_one,one_mul,
    SmoothPeriodicTest.Distribution.ofContinuous_coefficient,fourierCoeff_printedChirpAtPeriod,
    memlp_printedChirpCoefficient_iff]

/-- Actual period-L Fourier integrals retain the exact printed coefficients. -/
theorem intervalFourierCoefficient_printedChirpAtPeriod (m : ℤ) :
    intervalFourierCoefficient L (fun x : ℝ => printedChirpAtPeriod L (x : AddCircle L)) m =
      printedChirpCoefficient m := by
  rw [intervalFourierCoefficient_pullback_circle,fourierCoeff_printedChirpAtPeriod]

/-- The displayed formula with the required physical frequency 2*pi*n/L converges uniformly. -/
theorem tendstoUniformly_printedChirpAtPeriod_original :
    TendstoUniformly (fun (N : ℕ) (x : ℝ) => ∑ n ∈ Finset.Icc 2 N,
      (Complex.exp (Complex.I*((n : ℝ)*Real.log n)) /
        ((Real.sqrt n*(Real.log n)^2 : ℝ) : ℂ)) *
          Complex.exp (Complex.I*(2*Real.pi*n*x/L)))
      (fun x : ℝ => printedChirpAtPeriod L (x : AddCircle L)) atTop := by
  have h := tendstoUniformly_printedChirp_original.comp (fun x : ℝ => 2*x/L)
  have he (N : ℕ) (x : ℝ) :
      (∑ n ∈ Finset.Icc 2 N,
        (Complex.exp (Complex.I*((n : ℝ)*Real.log n)) /
          ((Real.sqrt n*(Real.log n)^2 : ℝ) : ℂ)) *
            Complex.exp (Complex.I*((n : ℝ)*Real.pi*(2*x/L)))) =
      ∑ n ∈ Finset.Icc 2 N,
        (Complex.exp (Complex.I*((n : ℝ)*Real.log n)) /
          ((Real.sqrt n*(Real.log n)^2 : ℝ) : ℂ)) *
            Complex.exp (Complex.I*(2*Real.pi*n*x/L)) := by
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    congr 1
    push_cast
    ring
  simp only [Function.comp_def,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_ofNat] at h he
  simpa only [printedChirpAtPeriod_coe,Complex.ofReal_mul,he] using h

end NLS.Fourier
