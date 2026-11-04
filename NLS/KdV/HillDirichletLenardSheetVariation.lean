import NLS.KdV.HillDirichletLenardVariation
import NLS.KdV.HillDirichletSheetVariation

/-! # Actual slope and moving-sheet velocities in Lenard directions

The mixed-state boundary term determines the fixed-energy slope variation.
Together with the actual Wronskian energy identity it determines the moving
signed sheet even when the sheet value vanishes at a terminal band edge.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory MvPolynomial
open scoped ContDiff
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.DifferentialPolynomial
namespace NLS.KdV

/-- The actual scalar forcing pairing along a physical polynomial field. -/
theorem hillScalar_polynomialDirection_pairing
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (P : DifferentialPolynomial.Polynomial) (E : ℂ) (v w : ℂ × ℂ) :
    let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
    let X := hillPolynomialDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf P
    (∫ x in (0:ℝ)..1,-(hillPhysicalDirection X).ofLp.2 x*
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt E) v) x).1*
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt E) w) x).1)=
      ∫ x in (0:ℝ)..1,(classicalHillFlow (hillUnitPotentialCurve Q) E v x).1*
        (classicalHillFlow (hillUnitPotentialCurve Q) E w x).1*
        evaluate (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0 P x := by
  dsimp only
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_polynomialDirection _ hf hp P,
    ae_restrict_mem measurableSet_Ioc] with x hx hxi
  rw [hx]
  have hx' : x∈Icc (0:ℝ) 1 := ⟨hxi.1.le,hxi.2⟩
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',hillL2FrequencyStateCurve_eq_classical,complex_sqrt_sq]
  ring

/-- The actual fixed-energy endpoint slope has its exact Lenard velocity,
with no division by a sheet value or gap-opening assumption. -/
theorem fderiv_hillL2DirichletSlope_lenardDirection
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (P : DifferentialPolynomial.Polynomial) (E : ℂ)
    (hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) E=0) :
    let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
    let X := hillPolynomialDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf (hillLenardPolynomial E P)
    (fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p E) q) X=
      -2*evaluate (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0 P 0*
        (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2 := by
  dsimp only
  let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
  let f := fun x : ℝ => Q (x : AddCircle (2:ℝ))
  let X := hillPolynomialDirection f hf (hillLenardPolynomial E P)
  let β := hillL2DirichletSlope q E
  let χ := (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2
  have hzC : (classicalHillFlow (scalarPotentialCurve f hf.continuous) E (0,1) 1).1=0 := by
    rw [hillL2DirichletCharacteristic_eq_classical] at hz
    exact hz
  have hS : (∫ x in (0:ℝ)..1,-(hillPhysicalDirection X).ofLp.2 x*
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) x).1^2)=
      -2*evaluate f 0 P 0*(β^2-1) := by
    calc
      _ = (∫ x in (0:ℝ)..1,-(hillPhysicalDirection X).ofLp.2 x*
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) x).1*
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) x).1) := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := by
        rw [hillScalar_polynomialDirection_pairing Q hf hp (hillLenardPolynomial E P) E (0,1) (0,1)]
        have hs := integral_classicalHillDirichletSquare_lenard f hf hp E P hzC
        rw [show scalarPotentialCurve f hf.continuous=hillUnitPotentialCurve Q from rfl] at hs
        dsimp only [β,q]
        rw [hillL2DirichletSlope_eq_classical]
        convert hs using 1
        apply intervalIntegral.integral_congr
        intro x _
        ring
  have hCS : (∫ x in (0:ℝ)..1,-(hillPhysicalDirection X).ofLp.2 x*
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0)) x).1*
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) x).1)=
      -2*evaluate f 0 P 0*χ*β := by
    rw [hillScalar_polynomialDirection_pairing Q hf hp (hillLenardPolynomial E P) E (1,0) (0,1)]
    have hc := integral_classicalHillDirichletMixed_lenard f hf hp E P hzC
    dsimp only [χ,β,q]
    rw [hillL2DirichletSlope_eq_classical,hillL2FrequencyStateCurve_eq_classical,complex_sqrt_sq]
    exact hc
  change (fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p E) q) X= -2*evaluate f 0 P 0*χ
  rw [fderiv_hillL2DirichletSlope_integral,hS,hCS]
  change -χ*(-2*evaluate f 0 P 0*(β^2-1))+β*(-2*evaluate f 0 P 0*χ*β)=_
  ring

/-- At a trace-stationary tangent, the fixed-energy sheet derivative is
exactly twice the actual slope derivative. -/
theorem fderiv_hillDirichletSheetRoot_of_trace_zero (q : Coeff 2) (E : ℂ) (v : Coeff 2)
    (hzero : (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) v=0) :
    (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p E) q) v=
      2*((fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p E) q) v) := by
  have hβ := (analyticOnNhd_hillL2DirichletSlope_joint (E,q) (mem_univ _)).comp
    (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
  have hΔ := (analyticOnNhd_hillL2Discriminant_joint (E,q) (mem_univ _)).comp
    (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L v)
    ((hβ.differentiableAt.hasFDerivAt.const_smul (2 : ℂ)).sub hΔ.differentiableAt.hasFDerivAt).fderiv
  change (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p E) q) v=
    2*((fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p E) q) v)-
      ((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) v) at hd
  simpa only [hzero,sub_zero] using hd

/-- The moving signed sheet has the actual normalized Lenard velocity,
including terminal band edges. No division by its value occurs. -/
theorem hillDirichletSheetRoot_moving_lenard_velocity
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)),
      hillL2DirichletCharacteristic p (a p)=0) (P : DifferentialPolynomial.Polynomial) :
    let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
    let E := a q
    (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (a p)) q)
      (hillPolynomialDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf (hillLenardPolynomial E P))=
      (hillL2Discriminant q E*deriv (hillL2Discriminant q) E)*
        (-2*evaluate (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 0 P 0/deriv (hillL2DirichletCharacteristic q) E) := by
  dsimp only
  let q := SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)
  let E := a q
  let f := fun x : ℝ => Q (x : AddCircle (2:ℝ))
  let X := hillPolynomialDirection f hf (hillLenardPolynomial E P)
  let A := evaluate f 0 P 0
  let d := deriv (hillL2DirichletCharacteristic q) E
  let χ := (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2
  let K := -2*A/d
  have hz0 : hillL2DirichletCharacteristic q E=0 := hz.self_of_nhds
  have hd : d≠0 := hillL2DirichletCharacteristic_deriv_ne_zero q hr E hz0
  have hβ := fderiv_hillL2DirichletSlope_lenardDirection Q hf hp P E hz0
  change (fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p E) q) X= -2*A*χ at hβ
  have hμ := hillDirichlet_branch_fderiv_lenard_sheet_velocity Q hf hp hr a ha hz P
  change (fderiv ℂ a q) X=hillDirichletSheetRoot q E*K at hμ
  have hfixed := fderiv_hillDirichletSheetRoot_of_trace_zero q E X
    (fderiv_hillL2Discriminant_lenardDirection_eq_zero Q hf hp P E)
  have hF : DifferentiableAt ℂ (fun t : ℂ × Coeff 2 => hillDirichletSheetRoot t.2 t.1) (a q,q) :=
    (analyticOnNhd_hillDirichletSheetRoot_joint _ (mem_univ _)).differentiableAt
  have hm := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L X)
    (fderiv_moving_spectral_parameter (fun t : ℂ × Coeff 2 => hillDirichletSheetRoot t.2 t.1) a q hF ha.differentiableAt)
  change (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (a p)) q) X=
    (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p E) q) X+
      deriv (hillDirichletSheetRoot q) E*((fderiv ℂ a q) X) at hm
  rw [hfixed,hβ,deriv_hillDirichletSheetRoot,hμ] at hm
  have hdet := hillDirichlet_wronskian_energy_factor q E hz0
  change 2*d*χ+(2*deriv (hillL2DirichletSlope q) E-deriv (hillL2Discriminant q) E)*hillDirichletSheetRoot q E=
    hillL2Discriminant q E*deriv (hillL2Discriminant q) E at hdet
  change (fderiv ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (a p)) q) X=
    (hillL2Discriminant q E*deriv (hillL2Discriminant q) E)*K
  rw [hm]
  calc
    _ = (2*d*χ+(2*deriv (hillL2DirichletSlope q) E-deriv (hillL2Discriminant q) E)*hillDirichletSheetRoot q E)*K := by
      dsimp only [K]
      field_simp [hd]
      ring
    _ = _ := by rw [hdet]

end NLS.KdV
