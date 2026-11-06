import NLS.KdV.HillL2TraceGradients
import NLS.ComplexAnalysis.QuadraticDividedDifference
import NLS.KdV.HillDirichletGardnerBrackets
import NLS.KdV.HillDirichletSheetRoot

/-! # The actual Dirichlet / discriminant Gardner bracket

Real period-one Fourier truncations transfer the actual scalar boundary
identity to rough Dirichlet states. The proved branch gradient and physical
trace gradient then give the normalized Gardner pairing.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
namespace NLS.KdV

private def stateTracePairing (A : Curve (ℂ × ℂ)) (G : Curve ℂ) : ℂ :=
  unitComplexCurveIntegral ((((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp A)^2)*G)

private theorem stateTracePairing_eq_integral (A : Curve (ℂ × ℂ)) (G : Curve ℂ) :
    stateTracePairing A G=∫ x in (0 : ℝ)..1,(extend A x).1^2*extend G x := rfl

private theorem continuous_stateTracePairing :
    Continuous (fun p : Curve (ℂ × ℂ) × Curve ℂ => stateTracePairing p.1 p.2) :=
  unitComplexCurveIntegral.continuous.comp
    ((((ContinuousMap.continuous_postcomp (ContinuousMap.fst : C(ℂ × ℂ,ℂ))).comp
      continuous_fst).pow 2).mul continuous_snd)

private theorem stateTracePairing_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (w z : ℂ) :
    stateTracePairing
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w (0,1))
      (hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z)=
      ∫ x in (0 : ℝ)..1, (classicalHillFlow (hillUnitPotentialCurve Q) (w^2) (0,1) x).1^2*
        classicalHillTracePairingKernelDx (hillUnitPotentialCurve Q) (z^2) x := by
  rw [stateTracePairing_eq_integral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',hillL2FrequencyStateCurve_eq_classical,
    hillL2TraceGradientSpatialCurve_eq_classical]

private theorem stateTracePairing_dirichlet_boundary_finite
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (z : ℂ) (N : ℕ) :
    let r := hillRealPeriodOneTruncate N q
    2*((hillDirichletEnergy r.val r.property.1 r.property.2 n hn : ℂ)-z^2)*
      stateTracePairing (hillDirichletStateCurve r n hn)
        (hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff r.val) z)=
      ((hillL2DirichletSlope (SpectralWeight.one.toCoeff r.val)
        (hillDirichletEnergy r.val r.property.1 r.property.2 n hn))^2-1)*
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff r.val) (z^2) := by
  let a (p : RealPeriodOneHillPotential) : ℂ := hillDirichletEnergy p.val p.property.1 p.property.2 n hn
  let P (p : RealPeriodOneHillPotential) := SpectralWeight.one.toCoeff p.val
  let r := hillRealPeriodOneTruncate N q
  let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) (hillRealPeriodOneTruncationFinsupp N q))
  have he : hillContinuousCoefficients Q=r.val := hillContinuousCoefficients_realPeriodOneTruncation N q
  have hz : hillL2DirichletCharacteristic (P r) (a r)=0 :=
    hillDirichletEnergy_zero r.val r.property.1 r.property.2 n hn
  change hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff r.val) (a r)=0 at hz
  rw [← he,hillL2DirichletCharacteristic_eq_classical] at hz
  change 2*(a r-z^2)*stateTracePairing
    (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (a r)) (0,1))
    (hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff r.val) z)=
      ((hillL2DirichletSlope (SpectralWeight.one.toCoeff r.val) (a r))^2-1)*
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff r.val) (z^2)
  rw [← he,stateTracePairing_eq_classical,complex_sqrt_sq,
    hillL2DirichletSlope_eq_classical,hillL2DirichletCharacteristic_eq_classical]
  exact classicalHill_dirichlet_traceKernel_pairing (hillUnitPotentialCurve Q) (a r) (z^2) hz

private def dirichletTraceLeft (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (z : ℂ) : ℂ :=
  2*((hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)-z^2)*
    stateTracePairing (hillDirichletStateCurve q n hn)
      (hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) z)

private def dirichletTraceRight (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (z : ℂ) : ℂ :=
  ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2-1)*
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) (z^2)

private theorem continuous_dirichletTraceLeft (n : ℕ) (hn : 1≤n) (z : ℂ) :
    Continuous (fun q : RealPeriodOneHillPotential => dirichletTraceLeft q n hn z) := by
  let a (p : RealPeriodOneHillPotential) : ℂ := hillDirichletEnergy p.val p.property.1 p.property.2 n hn
  let P (p : RealPeriodOneHillPotential) := SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have ha : Continuous a := Complex.continuous_ofReal.comp (continuous_hillDirichletEnergy n hn)
  have hpair : Continuous (fun p => stateTracePairing (hillDirichletStateCurve p n hn)
      (hillL2TraceGradientSpatialCurve (P p) z)) := by
    convert! continuous_stateTracePairing.comp ((continuous_hillDirichletStateCurve n hn).prodMk
      ((continuous_hillL2TraceGradientSpatialCurve z).comp hP)) using 1
  convert! (continuous_const.mul (ha.sub continuous_const)).mul hpair using 1

private theorem continuous_dirichletTraceRight (n : ℕ) (hn : 1≤n) (z : ℂ) :
    Continuous (fun q : RealPeriodOneHillPotential => dirichletTraceRight q n hn z) := by
  let a (p : RealPeriodOneHillPotential) : ℂ := hillDirichletEnergy p.val p.property.1 p.property.2 n hn
  let P (p : RealPeriodOneHillPotential) := SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have ha : Continuous a := Complex.continuous_ofReal.comp (continuous_hillDirichletEnergy n hn)
  have hcSlope : Continuous (fun x : ℂ × Coeff 2 => hillL2DirichletSlope x.2 x.1) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (analyticOnNhd_hillL2DirichletSlope_joint x (mem_univ _)).continuousAt)
  have hcChar : Continuous (fun x : ℂ × Coeff 2 => hillL2DirichletCharacteristic x.2 x.1) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (analyticOnNhd_hillL2DirichletCharacteristic_joint x (mem_univ _)).continuousAt)
  have hSlope : Continuous (fun p : RealPeriodOneHillPotential => hillL2DirichletSlope (P p) (a p)) := by
    convert! hcSlope.comp (ha.prodMk hP) using 1
  have hChar : Continuous (fun p : RealPeriodOneHillPotential => hillL2DirichletCharacteristic (P p) (z^2)) := by
    convert! hcChar.comp (continuous_const.prodMk hP) using 1
  convert! ((hSlope.pow 2).sub continuous_const).mul hChar using 1


private theorem stateTracePairing_dirichlet_boundary
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (z : ℂ) :
    2*((hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)-z^2)*
      stateTracePairing (hillDirichletStateCurve q n hn)
        (hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) z)=
      ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2-1)*
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) (z^2) := by
  let F (p : RealPeriodOneHillPotential) := dirichletTraceLeft p n hn z-dirichletTraceRight p n hn z
  have hF : Continuous F := by
    convert! (continuous_dirichletTraceLeft n hn z).sub (continuous_dirichletTraceRight n hn z) using 1
  have hfinite (N : ℕ) : F (hillRealPeriodOneTruncate N q)=0 :=
    sub_eq_zero.mpr (stateTracePairing_dirichlet_boundary_finite q n hn z N)
  have ht := hF.continuousAt.tendsto.comp (tendsto_hillRealPeriodOneTruncate q)
  have heq : (fun N : ℕ => F (hillRealPeriodOneTruncate N q))=(fun _ : ℕ => (0 : ℂ)) := funext hfinite
  change Tendsto (fun N : ℕ => F (hillRealPeriodOneTruncate N q)) atTop (𝓝 (F q)) at ht
  rw [heq] at ht
  exact sub_eq_zero.mp (tendsto_nhds_unique ht tendsto_const_nhds)

/-- At an actual Dirichlet zero the defined sheet root has the signed slope normalization. -/
theorem hillDirichletSheetRoot_eq_slope_sub_inv (q : Coeff 2) (a : ℂ)
    (hz : hillL2DirichletCharacteristic q a=0) :
    hillDirichletSheetRoot q a=hillL2DirichletSlope q a-(hillL2DirichletSlope q a)⁻¹ := by
  let z := Complex.sqrt a
  let e : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  let c := (hillL2FrequencyStateCurve q z (1,0) e).1
  let β := hillL2DirichletSlope q a
  have hs : (hillL2FrequencyStateCurve q z (0,1) e).1=0 := hz
  have hw := hillL2FrequencyStateCurve_wronskian q z e
  rw [hs,zero_mul,sub_zero] at hw
  change c*β=1 at hw
  have hβ : β≠0 := by intro h;rw [h,mul_zero] at hw;exact zero_ne_one hw
  have hc : c=β⁻¹ := by
    have hh := congrArg (fun v : ℂ => v*β⁻¹) hw
    simpa only [mul_assoc,mul_inv_cancel₀ hβ,mul_one,one_mul] using hh
  have ht := hillL2FrequencyStateCurve_trace q z
  rw [← hillL2Discriminant_sq,complex_sqrt_sq] at ht
  change c+β=hillL2Discriminant q a at ht
  change 2*β-hillL2Discriminant q a=β-β⁻¹
  rw [← ht,hc]
  ring

/-- Literal scalar Gardner pairing of the actual normalized Dirichlet branch
and discriminant gradients, with their physical unit-interval normalization. -/
def hillDirichletDiscriminantGardnerBracket
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (b : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*
    deriv (extend (hillL2TraceGradientCurve (SpectralWeight.one.toCoeff q.val) (Complex.sqrt b))) x

private theorem hillDirichletDiscriminantGardnerBracket_eq_state_pairing
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (b : ℂ) :
    hillDirichletDiscriminantGardnerBracket q n hn b=
      (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
        stateTracePairing (hillDirichletStateCurve q n hn)
          (hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) (Complex.sqrt b)) := by
  rw [stateTracePairing_eq_integral,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillL2TraceGradientCurve (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt b)] with x hx
  rw [hx.deriv]
  change ((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
    (extend (hillDirichletStateCurve q n hn) x).1^2)*_= _
  ring

/-- The actual normalized bracket retains the exact boundary factors, including the diagonal. -/
theorem hillDirichletDiscriminantGardnerBracket_mass_identity
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (b : ℂ) :
    2*((hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)-b)*
      (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)*
        hillDirichletDiscriminantGardnerBracket q n hn b=
      ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2-1)*
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) b := by
  have hM : (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)≠0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (hillL2FrequencyStateCurve_mass_pos (SpectralWeight.one.toCoeff q.val)
      (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)
      (by intro h;have hh := congrArg Prod.snd h;norm_num at hh)).ne'
  rw [hillDirichletDiscriminantGardnerBracket_eq_state_pairing]
  calc
    _ = 2*((hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)-b)*
        stateTracePairing (hillDirichletStateCurve q n hn)
          (hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) (Complex.sqrt b)) := by
      simp [mul_assoc,hM]
    _ = _ := by
      simpa only [complex_sqrt_sq] using stateTracePairing_dirichlet_boundary q n hn (Complex.sqrt b)

/-- Physical mass normalization gives the exact signed sheet coefficient. -/
theorem hillDirichletDiscriminantGardnerBracket_sheet_identity
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (b : ℂ) :
    let a : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let p := SpectralWeight.one.toCoeff q.val
    2*(a-b)*deriv (hillL2DirichletCharacteristic p) a*
      hillDirichletDiscriminantGardnerBracket q n hn b=
        hillL2DirichletCharacteristic p b*
          (hillL2DirichletSlope p a-(hillL2DirichletSlope p a)⁻¹) := by
  dsimp only
  let a : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  let p := SpectralWeight.one.toCoeff q.val
  let d := deriv (hillL2DirichletCharacteristic p) a
  let β := hillL2DirichletSlope p a
  have hz : hillL2DirichletCharacteristic p a=0 :=
    hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
  have hβ : β≠0 := hillL2DirichletSlope_ne_zero_at_dirichlet_zero p q.property.2 a hz
  have hm := hillL2Dirichlet_derivative_normalization p q.property.2 a hz
  change d*β=(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) at hm
  have hb := hillDirichletDiscriminantGardnerBracket_mass_identity q n hn b
  change 2*(a-b)*(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)*
    hillDirichletDiscriminantGardnerBracket q n hn b=(β^2-1)*hillL2DirichletCharacteristic p b at hb
  rw [← hm] at hb
  change 2*(a-b)*d*hillDirichletDiscriminantGardnerBracket q n hn b=
    hillL2DirichletCharacteristic p b*(β-β⁻¹)
  apply (mul_right_cancel₀ hβ)
  calc
    _ = 2*(a-b)*(d*β)*hillDirichletDiscriminantGardnerBracket q n hn b := by ring
    _ = (β^2-1)*hillL2DirichletCharacteristic p b := hb
    _ = (hillL2DirichletCharacteristic p b*(β-β⁻¹))*β := by
      field_simp [hβ]

/-- Off the energy diagonal, the actual Dirichlet / trace bracket is the source quotient. -/
theorem hillDirichletDiscriminantGardnerBracket_eq_quotient
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (b : ℂ)
    (hab : (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)≠b) :
    let a : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let p := SpectralWeight.one.toCoeff q.val
    hillDirichletDiscriminantGardnerBracket q n hn b=
      (hillL2DirichletCharacteristic p b*(hillL2DirichletSlope p a-(hillL2DirichletSlope p a)⁻¹))/
        (2*(a-b)*deriv (hillL2DirichletCharacteristic p) a) := by
  dsimp only
  have hz := hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
  have hd := hillL2DirichletCharacteristic_deriv_ne_zero (SpectralWeight.one.toCoeff q.val)
    q.property.2 (hillDirichletEnergy q.val q.property.1 q.property.2 n hn) hz
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hab)) hd)).mpr
  exact (mul_comm _ _).trans (hillDirichletDiscriminantGardnerBracket_sheet_identity q n hn b)

/-- The actual sheet-root form of the source bracket, with the energy diagonal retained. -/
theorem hillDirichletDiscriminantGardnerBracket_root_identity
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (b : ℂ) :
    let a : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let p := SpectralWeight.one.toCoeff q.val
    2*(a-b)*deriv (hillL2DirichletCharacteristic p) a*
      hillDirichletDiscriminantGardnerBracket q n hn b=
        hillL2DirichletCharacteristic p b*hillDirichletSheetRoot p a := by
  dsimp only
  rw [hillDirichletSheetRoot_eq_slope_sub_inv _ _
    (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn)]
  exact hillDirichletDiscriminantGardnerBracket_sheet_identity q n hn b

/-- The normalized off-diagonal bracket with the actual sheet root. -/
theorem hillDirichletDiscriminantGardnerBracket_eq_sheet_quotient
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (b : ℂ)
    (hab : (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)≠b) :
    let a : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let p := SpectralWeight.one.toCoeff q.val
    hillDirichletDiscriminantGardnerBracket q n hn b=
      (hillL2DirichletCharacteristic p b*hillDirichletSheetRoot p a)/
        (2*(a-b)*deriv (hillL2DirichletCharacteristic p) a) := by
  dsimp only
  rw [hillDirichletSheetRoot_eq_slope_sub_inv _ _
    (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn)]
  exact hillDirichletDiscriminantGardnerBracket_eq_quotient q n hn b hab

private theorem stateTracePairing_dirichlet_diagonal
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    let a : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let p := SpectralWeight.one.toCoeff q.val
    stateTracePairing (hillDirichletStateCurve q n hn)
      (hillL2TraceGradientSpatialCurve p (Complex.sqrt a))=
        -((hillL2DirichletSlope p a^2-1)/2)*deriv (hillL2DirichletCharacteristic p) a := by
  dsimp only
  let a : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  let p := SpectralWeight.one.toCoeff q.val
  let G (z : ℂ) := stateTracePairing (hillDirichletStateCurve q n hn) (hillL2TraceGradientSpatialCurve p z)
  have hG : Continuous G := by
    convert! continuous_stateTracePairing.comp
      (continuous_const.prodMk (continuous_hillL2TraceGradientSpatialCurve_frequency p)) using 1
  have hz : hillL2DirichletCharacteristic p a=0 :=
    hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
  apply value_of_quadratic_divided_difference (hillL2DirichletCharacteristic p) G a (Complex.sqrt a)
    ((hillL2DirichletSlope p a^2-1)/2) (deriv (hillL2DirichletCharacteristic p) a)
    (complex_sqrt_sq a)
    ((analyticOnNhd_hillL2DirichletCharacteristic p a (mem_univ _)).differentiableAt.hasDerivAt)
    hz hG.continuousAt
  intro w
  have hb := stateTracePairing_dirichlet_boundary q n hn w
  change 2*(a-w^2)*G w=(hillL2DirichletSlope p a^2-1)*hillL2DirichletCharacteristic p (w^2) at hb
  linear_combination hb/2

/-- The source quotient fills at the energy diagonal with its exact signed value. -/
theorem hillDirichletDiscriminantGardnerBracket_diagonal
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    let a : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    hillDirichletDiscriminantGardnerBracket q n hn a=
      -(hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) a)/2 := by
  dsimp only
  let a : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  let p := SpectralWeight.one.toCoeff q.val
  let d := deriv (hillL2DirichletCharacteristic p) a
  let β := hillL2DirichletSlope p a
  have hz : hillL2DirichletCharacteristic p a=0 :=
    hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
  have hd : d≠0 := hillL2DirichletCharacteristic_deriv_ne_zero p q.property.2 a hz
  have hβ : β≠0 := hillL2DirichletSlope_ne_zero_at_dirichlet_zero p q.property.2 a hz
  have hm := hillL2Dirichlet_derivative_normalization p q.property.2 a hz
  change d*β=(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) at hm
  rw [hillDirichletDiscriminantGardnerBracket_eq_state_pairing,stateTracePairing_dirichlet_diagonal,
    hillDirichletSheetRoot_eq_slope_sub_inv p a hz,← hm]
  change (d*β)⁻¹*(-((β^2-1)/2)*d)= -(β-β⁻¹)/2
  field_simp [hd,hβ]

end NLS.KdV
