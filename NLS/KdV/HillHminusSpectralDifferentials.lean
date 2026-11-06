import NLS.KdV.HillHminusOriginalSource

noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

/-- The actual H-minus-one discriminant is entire in its potential. -/
theorem analyticAt_hillHminusDiscriminant_source (q : PeriodOneHminusOne) (E : ℂ) :
    AnalyticAt ℂ (fun r => hillHminusDiscriminant r E) q :=
  (analyticOnNhd_hillHminusDiscriminant_joint (E,q) (mem_univ _)).comp
    (f := fun r : PeriodOneHminusOne => (E,r)) (analyticAt_const.prod analyticAt_id)

/-- The actual H-minus-one Dirichlet characteristic is entire in its potential. -/
theorem analyticAt_hillHminusDirichlet_source (q : PeriodOneHminusOne) (E : ℂ) :
    AnalyticAt ℂ (fun r => hillHminusDirichlet r E) q :=
  (analyticOnNhd_hillHminusDirichlet_joint (E,q) (mem_univ _)).comp
    (f := fun r : PeriodOneHminusOne => (E,r)) (analyticAt_const.prod analyticAt_id)

/-- Exact restriction of the genuine discriminant differential to the
original native Hilbert source directions. -/
theorem hillHminusDiscriminant_native_fderiv (q : Coeff 2) (E : ℂ) :
    fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant (hillNativeHilbertDirection a) E) q=
      (fderiv ℂ (fun r : PeriodOneHminusOne => hillHminusDiscriminant r E)
        (NLS.Poisson.hilbertToHminus q)).comp NLS.Poisson.hilbertToHminus := by
  have h := (analyticAt_hillHminusDiscriminant_source
    (NLS.Poisson.hilbertToHminus q) E).differentiableAt.hasFDerivAt.comp q
      NLS.Poisson.hilbertToHminus.hasFDerivAt
  have heq : (fun a : Coeff 2 => hillHminusDiscriminant (NLS.Poisson.hilbertToHminus a) E)=
      (fun a : Coeff 2 => hillL2Discriminant (hillNativeHilbertDirection a) E) :=
    funext (fun a => hillHminusDiscriminant_native_hilbert_agreement a E)
  simpa only [Function.comp_def,heq] using h.fderiv

/-- Exact restriction of the derivative-one Dirichlet differential to
original native Hilbert directions. -/
theorem hillHminusDirichlet_native_fderiv (q : Coeff 2) (E : ℂ) :
    fderiv ℂ (fun a : Coeff 2 => hillL2DirichletCharacteristic (hillNativeHilbertDirection a) E) q=
      (fderiv ℂ (fun r : PeriodOneHminusOne => hillHminusDirichlet r E)
        (NLS.Poisson.hilbertToHminus q)).comp NLS.Poisson.hilbertToHminus := by
  have h := (analyticAt_hillHminusDirichlet_source
    (NLS.Poisson.hilbertToHminus q) E).differentiableAt.hasFDerivAt.comp q
      NLS.Poisson.hilbertToHminus.hasFDerivAt
  have heq : (fun a : Coeff 2 => hillHminusDirichlet (NLS.Poisson.hilbertToHminus a) E)=
      (fun a : Coeff 2 => hillL2DirichletCharacteristic (hillNativeHilbertDirection a) E) :=
    funext (fun a => hillHminusDirichlet_native_hilbert_agreement a E)
  simpa only [Function.comp_def,heq] using h.fderiv

/-- The original physical discriminant differential, including its literal
source insertion, is the restricted H-minus-one differential. -/
theorem hillHminusDiscriminant_original_fderiv (q : Coeff 2) (E : ℂ) :
    (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant a E)
      (hillNativeHilbertDirection q)).comp hillNativeHilbertDirection=
      (fderiv ℂ (fun r : PeriodOneHminusOne => hillHminusDiscriminant r E)
        (NLS.Poisson.hilbertToHminus q)).comp NLS.Poisson.hilbertToHminus := by
  have ha := (analyticOnNhd_hillL2Discriminant_joint
    (E,hillNativeHilbertDirection q) (mem_univ _)).comp
      (f := fun a : Coeff 2 => (E,a)) (analyticAt_const.prod analyticAt_id)
  have h := ha.differentiableAt.hasFDerivAt.comp q hillNativeHilbertDirection.hasFDerivAt
  exact h.fderiv.symm.trans (hillHminusDiscriminant_native_fderiv q E)

/-- The original derivative-one physical characteristic has the same
exact restricted differential. -/
theorem hillHminusDirichlet_original_fderiv (q : Coeff 2) (E : ℂ) :
    (fderiv ℂ (fun a : Coeff 2 => hillL2DirichletCharacteristic a E)
      (hillNativeHilbertDirection q)).comp hillNativeHilbertDirection=
      (fderiv ℂ (fun r : PeriodOneHminusOne => hillHminusDirichlet r E)
        (NLS.Poisson.hilbertToHminus q)).comp NLS.Poisson.hilbertToHminus := by
  have ha := (analyticOnNhd_hillL2DirichletCharacteristic_joint
    (E,hillNativeHilbertDirection q) (mem_univ _)).comp
      (f := fun a : Coeff 2 => (E,a)) (analyticAt_const.prod analyticAt_id)
  have h := ha.differentiableAt.hasFDerivAt.comp q hillNativeHilbertDirection.hasFDerivAt
  exact h.fderiv.symm.trans (hillHminusDirichlet_native_fderiv q E)

/-- Every coefficient of the actual H-minus-one trace gradient is the
literal unit Fourier integral of the original physical trace gradient. -/
theorem hminusScalarGradient_hillDiscriminant_native_coefficients
    (q : Coeff 2) (E : ℂ) (k : ℤ) :
    (NLS.Poisson.hminusScalarGradient (fun r => hillHminusDiscriminant r E)
      (NLS.Poisson.hilbertToHminus q)).val k=
      Fourier.unitFourierCoefficient
        (NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve
          (hillNativeHilbertDirection q) E)) k := by
  have hs : NLS.Poisson.hilbertToHminus (lp.single 2 (-k) 1)=
      WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-k) 1) := by
    apply Subtype.ext
    funext j
    simp [NLS.Poisson.hilbertToHminus_apply,WeightedCoeff.ofFinsupp_apply,lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  have hm : hillNativeHilbertDirection (lp.single 2 (-k) 1)=lp.single 2 (2*(-k)) 1 := by
    change Coeff.insert (Coeff.parityEmbedding 0) (lp.single 2 (-k) 1)=_
    rw [Coeff.insert_single,Coeff.parityEmbedding_apply,add_zero]
  rw [NLS.Poisson.hminusScalarGradient_apply,←hs]
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (lp.single 2 (-k) 1))
    (hillHminusDiscriminant_original_fderiv q E)
  change (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant a E)
    (hillNativeHilbertDirection q)) (hillNativeHilbertDirection (lp.single 2 (-k) 1))=_ at he
  simp only [ContinuousLinearMap.comp_apply] at he
  rw [←he,hm,hillDiscriminantCotangent_single_integral]
  unfold Fourier.unitFourierCoefficient
  simp only [mul_neg]

end NLS.KdV
