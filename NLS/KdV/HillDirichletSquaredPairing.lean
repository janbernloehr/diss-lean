import NLS.KdV.HillStateJointContinuity
import NLS.KdV.HillRealPeriodOneTruncation
import NLS.ComplexAnalysis.ScalarStateSquaredPairing
import NLS.KdV.ClassicalHillDirichletBrackets

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ComplexConjugate ENNReal

namespace NLS.KdV

theorem scalarStateSquaredPairing_hill_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (z w : ℂ) :
    scalarStateSquaredPairing
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z (0,1))
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w (0,1))=
    ∫ x in (0 : ℝ)..1, (classicalHillFlow (hillUnitPotentialCurve Q) (z^2) (0,1) x).1^2*
      (classicalHillFlow (hillUnitPotentialCurve Q) (w^2) (0,1) x).1*
      (classicalHillFlow (hillUnitPotentialCurve Q) (w^2) (0,1) x).2 := by
  rw [scalarStateSquaredPairing_eq_integral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',hillL2FrequencyStateCurve_eq_classical]

theorem classicalHill_dirichlet_diagonal_squared_pairing_zero
    (q : Curve ℂ) (a : ℂ) (ha : (classicalHillFlow q a (0,1) 1).1=0) :
    (∫ x in (0 : ℝ)..1, (classicalHillFlow q a (0,1) x).1^2*
      (classicalHillFlow q a (0,1) x).1*(classicalHillFlow q a (0,1) x).2)=0 := by
  let A := classicalHillFlow q a (0,1)
  have hA : Continuous A := continuous_classicalHillFlow q a (0,1)
  have hd (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (A x).1^4)
      (4*((A t).1^2*(A t).1*(A t).2)) t.val := by
    have hf : HasDerivAt (fun x : ℝ => (A x).1) (A t).2 t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (0,1) t).fst
    convert! hf.pow 4 using 1
    ring
  have hc : Continuous (fun x : ℝ => (A x).1^4) := by fun_prop
  have hi : IntervalIntegrable (fun x : ℝ => 4*((A x).1^2*(A x).1*(A x).2)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hc.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hd ⟨x,hx.1.le,hx.2.le⟩) hi
  change (∫ x in (0 : ℝ)..1,4*((A x).1^2*(A x).1*(A x).2))=(A 1).1^4-(A 0).1^4 at h
  rw [intervalIntegral.integral_const_mul] at h
  have he : 4*(∫ x in (0 : ℝ)..1,(A x).1^2*(A x).1*(A x).2)=0 := by
    simpa [A,ha,classicalHillFlow_zero] using h
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

theorem classicalHill_dirichlet_squared_pairing_zero_all
    (q : Curve ℂ) (a b : ℂ)
    (ha : (classicalHillFlow q a (0,1) 1).1=0)
    (hb : (classicalHillFlow q b (0,1) 1).1=0) :
    (∫ x in (0 : ℝ)..1, (classicalHillFlow q a (0,1) x).1^2*
      (classicalHillFlow q b (0,1) x).1*(classicalHillFlow q b (0,1) x).2)=0 := by
  by_cases hab : a=b
  · subst b
    exact classicalHill_dirichlet_diagonal_squared_pairing_zero q a ha
  · exact classicalHill_dirichlet_squared_pairing_zero q a b hab ha hb

theorem scalarStateSquaredPairing_hillDirichletState_zero
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) :
    scalarStateSquaredPairing (hillDirichletStateCurve q n hn) (hillDirichletStateCurve q m hm)=0 := by
  let F (p : RealPeriodOneHillPotential) :=
    scalarStateSquaredPairing (hillDirichletStateCurve p n hn) (hillDirichletStateCurve p m hm)
  have hF : Continuous F := by
    convert! continuous_scalarStateSquaredPairing.comp
      ((continuous_hillDirichletStateCurve n hn).prodMk (continuous_hillDirichletStateCurve m hm)) using 1
  have hfinite (N : ℕ) : F (hillRealPeriodOneTruncate N q)=0 := by
    let r := hillRealPeriodOneTruncate N q
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) (hillRealPeriodOneTruncationFinsupp N q))
    let a : ℝ := hillDirichletEnergy r.val r.property.1 r.property.2 n hn
    let b : ℝ := hillDirichletEnergy r.val r.property.1 r.property.2 m hm
    have he : hillContinuousCoefficients Q=r.val := hillContinuousCoefficients_realPeriodOneTruncation N q
    have hza : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff r.val) a=0 :=
      hillDirichletEnergy_zero r.val r.property.1 r.property.2 n hn
    have hzb : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff r.val) b=0 :=
      hillDirichletEnergy_zero r.val r.property.1 r.property.2 m hm
    rw [← he,hillL2DirichletCharacteristic_eq_classical] at hza hzb
    change scalarStateSquaredPairing
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (a : ℂ)) (0,1))
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (b : ℂ)) (0,1))=0
    rw [← he,scalarStateSquaredPairing_hill_eq_classical,complex_sqrt_sq,complex_sqrt_sq]
    exact classicalHill_dirichlet_squared_pairing_zero_all (hillUnitPotentialCurve Q) a b hza hzb
  have ht := hF.continuousAt.tendsto.comp (tendsto_hillRealPeriodOneTruncate q)
  have heq : (fun N : ℕ => F (hillRealPeriodOneTruncate N q))=(fun _ : ℕ => (0 : ℂ)) := funext hfinite
  change Tendsto (fun N : ℕ => F (hillRealPeriodOneTruncate N q)) atTop (𝓝 (F q)) at ht
  rw [heq] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end NLS.KdV
