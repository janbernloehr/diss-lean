import NLS.KdV.HillDirichletCosineData
import NLS.KdV.ClassicalHillMixedPairings
import NLS.ComplexAnalysis.ScalarStateMixedPairing

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem scalarStateMixedPairing_hill_eq_classical
    (Q : C(AddCircle (2 : ℝ),ℂ)) (z w : ℂ) :
    scalarStateMixedPairing
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z (0,1))
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w (1,0))
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w (0,1))=
    ∫ x in (0 : ℝ)..1,(classicalHillFlow (hillUnitPotentialCurve Q) (z^2) (0,1) x).1^2*
      ((classicalHillFlow (hillUnitPotentialCurve Q) (w^2) (1,0) x).2*
          (classicalHillFlow (hillUnitPotentialCurve Q) (w^2) (0,1) x).1+
        (classicalHillFlow (hillUnitPotentialCurve Q) (w^2) (1,0) x).1*
          (classicalHillFlow (hillUnitPotentialCurve Q) (w^2) (0,1) x).2) := by
  rw [scalarStateMixedPairing_eq_integral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',hillL2FrequencyStateCurve_eq_classical]

theorem scalarStateMixedPairing_hillDirichlet_ne
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) (hne : n≠m) :
    scalarStateMixedPairing (hillDirichletStateCurve q n hn)
      (hillDirichletCosineCurve q m hm) (hillDirichletStateCurve q m hm)=0 := by
  let F (p : RealPeriodOneHillPotential) := scalarStateMixedPairing (hillDirichletStateCurve p n hn)
    (hillDirichletCosineCurve p m hm) (hillDirichletStateCurve p m hm)
  have hF : Continuous F := by
    convert! continuous_scalarStateMixedPairing.comp
      ((continuous_hillDirichletStateCurve n hn).prodMk
        ((continuous_hillDirichletCosineCurve m hm).prodMk (continuous_hillDirichletStateCurve m hm))) using 1
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
    have hab : (a : ℂ)≠(b : ℂ) := hillDirichletEnergy_ne_of_ne r n m hn hm hne
    rw [← he,hillL2DirichletCharacteristic_eq_classical] at hza hzb
    change scalarStateMixedPairing
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (a : ℂ)) (0,1))
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (b : ℂ)) (1,0))
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (b : ℂ)) (0,1))=0
    rw [← he,scalarStateMixedPairing_hill_eq_classical,complex_sqrt_sq,complex_sqrt_sq]
    exact classicalHill_dirichlet_mixed_pairing_zero_of_ne (hillUnitPotentialCurve Q) a b hab hza hzb
  have ht := hF.continuousAt.tendsto.comp (tendsto_hillRealPeriodOneTruncate q)
  have heq : (fun N : ℕ => F (hillRealPeriodOneTruncate N q))=(fun _ : ℕ => (0 : ℂ)) := funext hfinite
  change Tendsto (fun N : ℕ => F (hillRealPeriodOneTruncate N q)) atTop (𝓝 (F q)) at ht
  rw [heq] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem scalarStateMixedPairing_hillDirichlet_diagonal
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    scalarStateMixedPairing (hillDirichletStateCurve q n hn)
      (hillDirichletCosineCurve q n hn) (hillDirichletStateCurve q n hn)=
      -(scalarStateCrossMass (hillDirichletStateCurve q n hn) (hillDirichletStateCurve q n hn))/2 := by
  let F (p : RealPeriodOneHillPotential) := scalarStateMixedPairing (hillDirichletStateCurve p n hn)
    (hillDirichletCosineCurve p n hn) (hillDirichletStateCurve p n hn)+
    scalarStateCrossMass (hillDirichletStateCurve p n hn) (hillDirichletStateCurve p n hn)/2
  have hA := continuous_hillDirichletStateCurve n hn
  have hC := continuous_hillDirichletCosineCurve n hn
  have h1 : Continuous (fun p : RealPeriodOneHillPotential => scalarStateMixedPairing (hillDirichletStateCurve p n hn)
      (hillDirichletCosineCurve p n hn) (hillDirichletStateCurve p n hn)) := by
    convert! continuous_scalarStateMixedPairing.comp (hA.prodMk (hC.prodMk hA)) using 1
  have h2 : Continuous (fun p : RealPeriodOneHillPotential =>
      scalarStateCrossMass (hillDirichletStateCurve p n hn) (hillDirichletStateCurve p n hn)) := by
    convert! continuous_scalarStateCrossMass.comp (hA.prodMk hA) using 1
  have hF : Continuous F := h1.add (h2.div_const 2)
  have hfinite (N : ℕ) : F (hillRealPeriodOneTruncate N q)=0 := by
    let r := hillRealPeriodOneTruncate N q
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) (hillRealPeriodOneTruncationFinsupp N q))
    let a : ℝ := hillDirichletEnergy r.val r.property.1 r.property.2 n hn
    have he : hillContinuousCoefficients Q=r.val := hillContinuousCoefficients_realPeriodOneTruncation N q
    have hza : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff r.val) a=0 :=
      hillDirichletEnergy_zero r.val r.property.1 r.property.2 n hn
    rw [← he,hillL2DirichletCharacteristic_eq_classical] at hza
    change scalarStateMixedPairing
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (a : ℂ)) (0,1))
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (a : ℂ)) (1,0))
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (a : ℂ)) (0,1))+
      scalarStateCrossMass
        (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (a : ℂ)) (0,1))
        (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (a : ℂ)) (0,1))/2=0
    rw [← he,scalarStateMixedPairing_hill_eq_classical,scalarStateCrossMass_hill_eq_classical,complex_sqrt_sq]
    have hh := classicalHill_dirichlet_mixed_pairing_diagonal (hillUnitPotentialCurve Q) a hza
    simpa only [pow_two] using (eq_neg_iff_add_eq_zero.mp (by simpa only [neg_div,pow_two] using hh))
  have ht := hF.continuousAt.tendsto.comp (tendsto_hillRealPeriodOneTruncate q)
  have heq : (fun N : ℕ => F (hillRealPeriodOneTruncate N q))=(fun _ : ℕ => (0 : ℂ)) := funext hfinite
  change Tendsto (fun N : ℕ => F (hillRealPeriodOneTruncate N q)) atTop (𝓝 (F q)) at ht
  rw [heq] at ht
  have hz : F q=0 := tendsto_nhds_unique ht tendsto_const_nhds
  dsimp only [F] at hz
  linear_combination hz

end NLS.KdV
