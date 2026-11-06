import NLS.KdV.ClassicalHillDirichletSlopePairing
import NLS.KdV.HillDirichletSlopeVariation
import NLS.KdV.HillL2GardnerDirections

/-! # Actual rough Dirichlet slope variation in Gardner directions

Real Fourier truncations transfer the scalar mixed-state boundary identity.
The actual L2 source derivative and its physical Fourier representative then
identify the resulting pairing with the genuine rough Dirichlet slope.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
namespace NLS.KdV

def hillDirichletCosineStateCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) : Curve (ℂ × ℂ) :=
  hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (1,0)

theorem continuous_hillDirichletCosineStateCurve (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillDirichletCosineStateCurve q n hn) := by
  have hm : Continuous (fun q : RealPeriodOneHillPotential =>
      (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ),SpectralWeight.one.toCoeff q.val)) :=
    (continuous_complex_sqrt_real.comp (continuous_hillDirichletEnergy n hn)).prodMk
      (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val)
  convert! (continuous_hillL2FrequencyStateCurve_joint (1,0)).comp hm using 1

private def productTracePairing (C S : Curve (ℂ × ℂ)) (G : Curve ℂ) : ℂ :=
  unitComplexCurveIntegral (((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp C)*
    ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp S)*G)

private theorem productTracePairing_eq_integral (C S : Curve (ℂ × ℂ)) (G : Curve ℂ) :
    productTracePairing C S G=∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1*NLS.LinearVolterra.extend G x := rfl

private theorem continuous_productTracePairing :
    Continuous (fun p : (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) × Curve ℂ =>
      productTracePairing p.1.1 p.1.2 p.2) :=
  unitComplexCurveIntegral.continuous.comp
    ((((ContinuousMap.continuous_postcomp (ContinuousMap.fst : C(ℂ × ℂ,ℂ))).comp continuous_fst.fst).mul
      ((ContinuousMap.continuous_postcomp (ContinuousMap.fst : C(ℂ × ℂ,ℂ))).comp continuous_fst.snd)).mul continuous_snd)

private def slopeTracePairing (C S : Curve (ℂ × ℂ)) (G : Curve ℂ) : ℂ :=
  -(C ⟨1,by norm_num⟩).2*productTracePairing S S G+(S ⟨1,by norm_num⟩).2*productTracePairing C S G

private theorem continuous_slopeTracePairing :
    Continuous (fun p : (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) × Curve ℂ => slopeTracePairing p.1.1 p.1.2 p.2) := by
  have hχ : Continuous (fun p : (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) × Curve ℂ => (p.1.1 ⟨1,by norm_num⟩).2) :=
    ((continuous_eval_const _).comp continuous_fst.fst).snd
  have hβ : Continuous (fun p : (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) × Curve ℂ => (p.1.2 ⟨1,by norm_num⟩).2) :=
    ((continuous_eval_const _).comp continuous_fst.snd).snd
  have hm : Continuous (fun p : (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) × Curve ℂ => ((p.1.2,p.1.2),p.2)) :=
    (continuous_fst.snd.prodMk continuous_fst.snd).prodMk continuous_snd
  have hSS : Continuous (fun p : (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) × Curve ℂ => productTracePairing p.1.2 p.1.2 p.2) := by
    simpa only [Function.comp_def] using continuous_productTracePairing.comp hm
  change Continuous (fun p : (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) × Curve ℂ =>
    -(p.1.1 ⟨1,by norm_num⟩).2*productTracePairing p.1.2 p.1.2 p.2+
      (p.1.2 ⟨1,by norm_num⟩).2*productTracePairing p.1.1 p.1.2 p.2)
  exact (hχ.neg.mul hSS).add (hβ.mul continuous_productTracePairing)

private theorem productTracePairing_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (w z : ℂ) (v u : ℂ × ℂ) :
    productTracePairing
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w v)
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w u)
      (hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z)=
    ∫ x in (0 : ℝ)..1,(classicalHillFlow (hillUnitPotentialCurve Q) (w^2) v x).1*
      (classicalHillFlow (hillUnitPotentialCurve Q) (w^2) u x).1*
      classicalHillTracePairingKernelDx (hillUnitPotentialCurve Q) (z^2) x := by
  rw [productTracePairing_eq_integral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',hillL2FrequencyStateCurve_eq_classical,hillL2TraceGradientSpatialCurve_eq_classical]

private theorem slopeTracePairing_classical_boundary
    (Q : C(AddCircle (2 : ℝ),ℂ)) (a z : ℂ)
    (ha : (classicalHillFlow (hillUnitPotentialCurve Q) a (0,1) 1).1=0) :
    2*(a-z^2)*slopeTracePairing
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (Complex.sqrt a) (1,0))
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (Complex.sqrt a) (0,1))
      (hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z)=
    (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (Complex.sqrt a) (1,0) ⟨1,by norm_num⟩).2*
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2) := by
  simp only [slopeTracePairing,productTracePairing_eq_classical,hillL2FrequencyStateCurve_eq_classical,
    hillL2DirichletCharacteristic_eq_classical,complex_sqrt_sq]
  simp_rw [← pow_two]
  have hs := classicalHill_dirichlet_traceKernel_pairing (hillUnitPotentialCurve Q) a (z^2) ha
  have hc := classicalHill_dirichlet_cs_traceKernel_pairing (hillUnitPotentialCurve Q) a (z^2) ha
  linear_combination -(classicalHillFlow (hillUnitPotentialCurve Q) a (1,0) 1).2*hs+
    (classicalHillFlow (hillUnitPotentialCurve Q) a (0,1) 1).2*hc

private def dirichletSlopeLeft (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (z : ℂ) : ℂ :=
  2*((hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)-z^2)*slopeTracePairing
    (hillDirichletCosineStateCurve q n hn) (hillDirichletStateCurve q n hn)
    (hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) z)

private def dirichletSlopeRight (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (z : ℂ) : ℂ :=
  (hillDirichletCosineStateCurve q n hn ⟨1,by norm_num⟩).2*
    hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) (z^2)

private theorem continuous_dirichletSlopeLeft (n : ℕ) (hn : 1≤n) (z : ℂ) :
    Continuous (fun q : RealPeriodOneHillPotential => dirichletSlopeLeft q n hn z) := by
  have hP : Continuous (fun q : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff q.val) :=
    SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hT := continuous_slopeTracePairing.comp
    (((continuous_hillDirichletCosineStateCurve n hn).prodMk (continuous_hillDirichletStateCurve n hn)).prodMk
      ((continuous_hillL2TraceGradientSpatialCurve z).comp hP))
  exact (continuous_const.mul ((Complex.continuous_ofReal.comp (continuous_hillDirichletEnergy n hn)).sub continuous_const)).mul hT

private theorem continuous_dirichletSlopeRight (n : ℕ) (hn : 1≤n) (z : ℂ) :
    Continuous (fun q : RealPeriodOneHillPotential => dirichletSlopeRight q n hn z) := by
  have hP : Continuous (fun q : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff q.val) :=
    SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hchar : Continuous (fun t : ℂ × Coeff 2 => hillL2DirichletCharacteristic t.2 t.1) :=
    continuous_iff_continuousAt.mpr (fun t => (analyticOnNhd_hillL2DirichletCharacteristic_joint t (mem_univ _)).continuousAt)
  convert! (((continuous_eval_const _).comp (continuous_hillDirichletCosineStateCurve n hn)).snd).mul
    (hchar.comp (continuous_const.prodMk hP)) using 1

private theorem dirichletSlope_boundary_finite
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (z : ℂ) (N : ℕ) :
    dirichletSlopeLeft (hillRealPeriodOneTruncate N q) n hn z=dirichletSlopeRight (hillRealPeriodOneTruncate N q) n hn z := by
  let r := hillRealPeriodOneTruncate N q
  let a : ℂ := hillDirichletEnergy r.val r.property.1 r.property.2 n hn
  let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) (hillRealPeriodOneTruncationFinsupp N q))
  have he : hillContinuousCoefficients Q=r.val := hillContinuousCoefficients_realPeriodOneTruncation N q
  have hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff r.val) a=0 := hillDirichletEnergy_zero r.val r.property.1 r.property.2 n hn
  rw [← he,hillL2DirichletCharacteristic_eq_classical] at hz
  change 2*(a-z^2)*slopeTracePairing
    (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt a) (1,0))
    (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt a) (0,1))
    (hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff r.val) z)=
    (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt a) (1,0) ⟨1,by norm_num⟩).2*
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff r.val) (z^2)
  rw [← he]
  exact slopeTracePairing_classical_boundary Q a z hz

private theorem dirichletSlope_boundary (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (z : ℂ) :
    dirichletSlopeLeft q n hn z=dirichletSlopeRight q n hn z := by
  let F (p : RealPeriodOneHillPotential) := dirichletSlopeLeft p n hn z-dirichletSlopeRight p n hn z
  have hF : Continuous F := (continuous_dirichletSlopeLeft n hn z).sub (continuous_dirichletSlopeRight n hn z)
  have ht := hF.continuousAt.tendsto.comp (tendsto_hillRealPeriodOneTruncate q)
  have heq : (fun N : ℕ => F (hillRealPeriodOneTruncate N q))=(fun _ => (0 : ℂ)) :=
    funext (fun N => sub_eq_zero.mpr (dirichletSlope_boundary_finite q n hn z N))
  change Tendsto (fun N : ℕ => F (hillRealPeriodOneTruncate N q)) atTop (𝓝 (F q)) at ht
  rw [heq] at ht
  exact sub_eq_zero.mp (tendsto_nhds_unique ht tendsto_const_nhds)

private theorem fderivDirichletSlope_eq_pairing
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (b : ℂ) :
    let p := SpectralWeight.one.toCoeff q.val
    let a : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    (fderiv ℂ (fun r : Coeff 2 => hillL2DirichletSlope r a) p) (hillL2DiscriminantGardnerDirection p b)=
      slopeTracePairing (hillDirichletCosineStateCurve q n hn) (hillDirichletStateCurve q n hn)
        (hillL2TraceGradientSpatialCurve p (Complex.sqrt b)) := by
  let p := SpectralWeight.one.toCoeff q.val
  let a : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  let X := hillL2DiscriminantGardnerDirection p b
  let C := hillDirichletCosineStateCurve q n hn
  let S := hillDirichletStateCurve q n hn
  let G := hillL2TraceGradientSpatialCurve p (Complex.sqrt b)
  have hs : (∫ x in (0 : ℝ)..1,-(hillPhysicalDirection X).ofLp.2 x*(NLS.LinearVolterra.extend S x).1^2)=productTracePairing S S G := by
    rw [productTracePairing_eq_integral]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [hillPhysicalDirection_discriminantGardnerDirection p b] with x hx
    rw [hx]
    ring
  have hc : (∫ x in (0 : ℝ)..1,-(hillPhysicalDirection X).ofLp.2 x*(NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1)=
      productTracePairing C S G := by
    rw [productTracePairing_eq_integral]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [hillPhysicalDirection_discriminantGardnerDirection p b] with x hx
    rw [hx]
    ring
  have hfd := fderiv_hillL2DirichletSlope_integral p X a
  have hβ : hillL2DirichletSlope p a=(S ⟨1,by norm_num⟩).2 := rfl
  change (fderiv ℂ (fun r : Coeff 2 => hillL2DirichletSlope r a) p) X=
    -(C ⟨1,by norm_num⟩).2*(∫ x in (0 : ℝ)..1,-(hillPhysicalDirection X).ofLp.2 x*(NLS.LinearVolterra.extend S x).1^2)+
    hillL2DirichletSlope p a*(∫ x in (0 : ℝ)..1,-(hillPhysicalDirection X).ofLp.2 x*
      (NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1) at hfd
  rw [hs,hc,hβ] at hfd
  have hT : (fderiv ℂ (fun r : Coeff 2 => hillL2DirichletSlope r a) p) X=slopeTracePairing C S G := hfd
  exact hT

/-- Actual rough Dirichlet slope variation along the constructed Fourier
Gardner direction has the exact scalar endpoint factor, including bandedges. -/
theorem hillDirichletSlope_gardner_cross_identity
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (b : ℂ) :
    2*((hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)-b)*
      ((fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (SpectralWeight.one.toCoeff q.val))
          (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q.val) b))=
    (hillDirichletCosineStateCurve q n hn ⟨1,by norm_num⟩).2*
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) b := by
  rw [fderivDirichletSlope_eq_pairing q n hn b]
  have he := dirichletSlope_boundary q n hn (Complex.sqrt b)
  simpa only [dirichletSlopeLeft,dirichletSlopeRight,complex_sqrt_sq] using he

/-- The actual slope variation fills on the energy diagonal, including zero
energy; no continuity of a global square-root branch is assumed. -/
theorem hillDirichletSlope_gardner_diagonal
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let p := SpectralWeight.one.toCoeff q.val
    (fderiv ℂ (fun r : Coeff 2 => hillL2DirichletSlope r E) p) (hillL2DiscriminantGardnerDirection p E)=
      -((hillDirichletCosineStateCurve q n hn ⟨1,by norm_num⟩).2/2)*deriv (hillL2DirichletCharacteristic p) E := by
  let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  let p := SpectralWeight.one.toCoeff q.val
  let G (z : ℂ) := slopeTracePairing (hillDirichletCosineStateCurve q n hn) (hillDirichletStateCurve q n hn)
    (hillL2TraceGradientSpatialCurve p z)
  have hG : Continuous G := by
    convert! continuous_slopeTracePairing.comp
      ((continuous_const.prodMk continuous_const).prodMk (continuous_hillL2TraceGradientSpatialCurve_frequency p)) using 1
  change (fderiv ℂ (fun r : Coeff 2 => hillL2DirichletSlope r E) p)
    (hillL2DiscriminantGardnerDirection p E)=
      -((hillDirichletCosineStateCurve q n hn ⟨1,by norm_num⟩).2/2)*deriv (hillL2DirichletCharacteristic p) E
  rw [fderivDirichletSlope_eq_pairing q n hn E]
  apply value_of_quadratic_divided_difference (hillL2DirichletCharacteristic p) G E (Complex.sqrt E)
    ((hillDirichletCosineStateCurve q n hn ⟨1,by norm_num⟩).2/2) (deriv (hillL2DirichletCharacteristic p) E)
    (complex_sqrt_sq E)
    ((analyticOnNhd_hillL2DirichletCharacteristic p E (mem_univ _)).differentiableAt.hasDerivAt)
    (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn) hG.continuousAt
  intro w
  have hb := dirichletSlope_boundary q n hn w
  change 2*(E-w^2)*G w=(hillDirichletCosineStateCurve q n hn ⟨1,by norm_num⟩).2*
    hillL2DirichletCharacteristic p (w^2) at hb
  linear_combination hb/2

end NLS.KdV
