import NLS.KdV.HillSolutionProducts

/-! # Exact energy separation for a Dirichlet gradient and a solution product -/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem integral_hillDirichletGradient_productSpatial_energy
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (E : ℂ) (v w : ℂ × ℂ) :
    2*((hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)-E)*
      (∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*
        extend (hillSolutionProductSpatialCurve (SpectralWeight.one.toCoeff q.val) E v w) x) =
      ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2*
          hillSolutionProductCurve (SpectralWeight.one.toCoeff q.val) E v w ⟨1,by norm_num⟩-
        hillSolutionProductCurve (SpectralWeight.one.toCoeff q.val) E v w ⟨0,by norm_num⟩)/
          (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) := by
  let r := SpectralWeight.one.toCoeff q.val
  let mu : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  let A := hillDirichletStateCurve q n hn
  let B := hillL2FrequencyStateCurve r (Complex.sqrt E) v
  let C := hillL2FrequencyStateCurve r (Complex.sqrt E) w
  have hd (a : ℂ) (u : ℂ × ℂ) : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun t => (extend (hillL2FrequencyStateCurve r (Complex.sqrt a) u) t).1)
        (extend (hillL2FrequencyStateCurve r (Complex.sqrt a) u) x).2 x ∧
      HasDerivAt (fun t => (extend (hillL2FrequencyStateCurve r (Complex.sqrt a) u) t).2)
        ((hillIntervalPotential r x-a)*(extend (hillL2FrequencyStateCurve r (Complex.sqrt a) u) x).1) x := by
    filter_upwards [ae_hasDerivAt_hillL2FrequencyStateCurve_fst r (Complex.sqrt a) u,
      ae_hasDerivAt_hillL2FrequencyStateCurve_snd r (Complex.sqrt a) u] with x hf hg
    exact ⟨hf,by simpa only [complex_sqrt_sq] using hg⟩
  have hA0 : extend A 0 = (0,1) := by
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num),A,
      hillDirichletStateCurve,hillL2FrequencyStateCurve_zero]
  have hA1 : (extend A 1).1 = 0 := by
    simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num),
      A,hillDirichletStateCurve,hillL2DirichletCharacteristic,hillL2FrequencyStateDirichlet,hillL2FrequencyStateCurve_apply] using
      (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn)
  have hi := integral_scalarHill_squared_product_derivative (hillIntervalPotential r) mu E A B C
    (absolutelyContinuousOnInterval_hillStateCurve r (Complex.sqrt mu) (0,1))
    (absolutelyContinuousOnInterval_hillStateCurve r (Complex.sqrt E) v)
    (absolutelyContinuousOnInterval_hillStateCurve r (Complex.sqrt E) w)
    (hd mu (0,1)) (hd E v) (hd E w) (by rw [hA0]) hA1
  have he : (∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*
      extend (hillSolutionProductSpatialCurve r E v w) x) =
      (scalarStateMass A : ℂ)⁻¹*(∫ x in (0 : ℝ)..1,(extend A x).1^2*
        ((extend B x).2*(extend C x).1+(extend B x).1*(extend C x).2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    change ((scalarStateMass A : ℂ)⁻¹*(extend A x).1^2)*
      ((extend B x).2*(extend C x).1+(extend B x).1*(extend C x).2) = _
    ring
  change 2*(mu-E)*(∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*
    extend (hillSolutionProductSpatialCurve r E v w) x) = _
  rw [he]
  calc
    _ = (scalarStateMass A : ℂ)⁻¹*(2*(mu-E)*(∫ x in (0 : ℝ)..1,(extend A x).1^2*
      ((extend B x).2*(extend C x).1+(extend B x).1*(extend C x).2))) := by ring
    _ = _ := by
      rw [hi,hA0]
      have hs1 : (extend A 1).2 = hillL2DirichletSlope r mu := by
        simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num)]
        rfl
      have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
          (extend B t).1*(extend C t).1 = hillSolutionProductCurve r E v w ⟨t,ht⟩ := by
        simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ ht]
        rfl
      rw [hs1]
      dsimp only [Prod.snd]
      simp only [one_pow,one_mul]
      rw [mul_assoc ((hillL2DirichletSlope r mu)^2),hp 1 (by norm_num),hp 0 (by norm_num)]
      ring


end NLS.KdV
