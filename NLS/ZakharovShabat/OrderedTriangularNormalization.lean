import NLS.ZakharovShabat.OrderedTriangularMonodromy
import NLS.ZakharovShabat.SourceBalancedHeightReduction

/-! # Prescribing a periodic eigenvalue by ordered triangular normalization

A nonzero product of the two interaction integrals determines an explicit
rescaling of the upper source component for which the chosen parameter is
an actual periodic eigenvalue. The coefficient identities retain the norm
cost of the rescaling. They do not establish a printed-height violation.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Multiply only the upper physical coupling. -/
def scaleUpperCurve (c : ℂ) (Φ : Curve (ℂ × ℂ)) : Curve (ℂ × ℂ) where
  toFun t := (c*(Φ t).1,(Φ t).2)
  continuous_toFun := by fun_prop

@[simp] theorem extend_scaleUpperCurve (c : ℂ) (Φ : Curve (ℂ × ℂ)) (t : ℝ) :
    extend (scaleUpperCurve c Φ) t = (c*(extend Φ t).1,(extend Φ t).2) := rfl

/-- Upper-component scaling preserves the ordered support condition. -/
theorem HasOrderedTriangularSupport.scaleUpper {Φ : Curve (ℂ × ℂ)} {s : ℝ}
    (hΦ : HasOrderedTriangularSupport Φ s) (c : ℂ) :
    HasOrderedTriangularSupport (scaleUpperCurve c Φ) s := by
  intro t
  exact ⟨(hΦ t).1,fun ht => by change c*(Φ t).1 = 0; rw [(hΦ t).2 ht,mul_zero]⟩

@[simp] theorem upperInteractionPrimitive_scaleUpper (c : ℂ) (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    upperInteractionPrimitive (scaleUpperCurve c Φ) z t = c*upperInteractionPrimitive Φ z t := by
  unfold upperInteractionPrimitive
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [extend_scaleUpperCurve]
  dsimp
  ring

@[simp] theorem lowerInteractionPrimitive_scaleUpper (c : ℂ) (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    lowerInteractionPrimitive (scaleUpperCurve c Φ) z t = lowerInteractionPrimitive Φ z t := rfl

/-- The exact upper-coupling factor enforcing the periodic trace level. -/
def orderedPeriodicNormalization (Φ : Curve (ℂ × ℂ)) (z : ℂ) : ℂ :=
  -(exp (-I*z)-1)^2/(upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1)

/-- The normalized product is the precise periodic characteristic equation. -/
theorem orderedPeriodicNormalization_product (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (hprod : upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1 ≠ 0) :
    upperInteractionPrimitive (scaleUpperCurve (orderedPeriodicNormalization Φ z) Φ) z 1*
      lowerInteractionPrimitive (scaleUpperCurve (orderedPeriodicNormalization Φ z) Φ) z 1 =
        -(exp (-I*z)-1)^2 := by
  rw [upperInteractionPrimitive_scaleUpper, lowerInteractionPrimitive_scaleUpper, mul_assoc]
  exact div_mul_cancel₀ _ hprod

/-- This is the trace of the actual monodromy after normalization. -/
theorem classicalDiscriminant_orderedPeriodicNormalization (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    {s : ℝ} (hΦ : HasOrderedTriangularSupport Φ s)
    (hprod : upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1 ≠ 0) :
    classicalDiscriminant (scaleUpperCurve (orderedPeriodicNormalization Φ z) Φ) z = 2 := by
  have h := (classicalDiscriminant_orderedTriangular_level_iff
    (scaleUpperCurve (orderedPeriodicNormalization Φ z) Φ) z (hΦ.scaleUpper _) 1 (by norm_num)).mpr
      (orderedPeriodicNormalization_product Φ z hprod)
  simpa only [mul_one] using h

/-- The normalization's size is exposed for later Fourier-norm estimates. -/
theorem norm_orderedPeriodicNormalization (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    ‖orderedPeriodicNormalization Φ z‖ =
      ‖exp (-I*z)-1‖^2/(‖upperInteractionPrimitive Φ z 1‖*‖lowerInteractionPrimitive Φ z 1‖) := by
  simp [orderedPeriodicNormalization, norm_pow]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The coefficient-space operation changes only the upper source component. -/
def scaleUpperSource (c : ℂ) (φ : CoeffPair p) : CoeffPair p :=
  WithLp.toLp p (c • φ.fst,φ.snd)

omit [Fact (1 ≤ p)] in
@[simp] theorem scaleUpperSource_fst (c : ℂ) (φ : CoeffPair p) :
    (scaleUpperSource c φ).fst = c • φ.fst := rfl

omit [Fact (1 ≤ p)] in
@[simp] theorem scaleUpperSource_snd (c : ℂ) (φ : CoeffPair p) :
    (scaleUpperSource c φ).snd = φ.snd := rfl

/-- The exact original source norm, with no conversion to a maximum or sum norm. -/
theorem norm_scaleUpperSource_rpow (hp : p ≠ ⊤) (c : ℂ) (φ : CoeffPair p) :
    ‖scaleUpperSource c φ‖^p.toReal = (‖c‖*‖φ.fst‖)^p.toReal+‖φ.snd‖^p.toReal := by
  rw [norm_withLp_prod_rpow hp, scaleUpperSource_fst, scaleUpperSource_snd, norm_smul]

/-- Period doubling keeps the same single-component scaling. -/
theorem periodOnePotential_scaleUpperSource (c : ℂ) (φ : CoeffPair p) :
    periodOnePotential (scaleUpperSource c φ) =
      (c • (periodOnePotential φ).1,(periodOnePotential φ).2) := by
  simp [periodOnePotential_apply]

/-- The coefficient rescaling realizes the intended continuous physical potential. -/
theorem physicalBase_scaleUpperSource (c : ℂ) (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) :
    physicalBase (periodOnePotential (scaleUpperSource c φ)) =ᵐ[volume.restrict (Ioc 0 1)]
      extend (scaleUpperCurve c Φ) := by
  have hs := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (physicalBase_smul c (periodOnePotential φ))
  rw [periodOnePotential_scaleUpperSource]
  filter_upwards [hs,hΦ] with t hsm hφ
  apply Prod.ext
  · exact (congrArg Prod.fst hsm).trans (congrArg (fun v : ℂ × ℂ => c*v.1) hφ)
  · change (physicalBase (periodOnePotential φ) t).2 = (extend Φ t).2
    exact congrArg Prod.snd hφ

/-- Normalization gives an actual periodic eigenvalue at every finite exponent at least two.
The assumption identifies a genuine continuous representative of the original source. -/
theorem source_mem_periodicSpectrum_orderedPeriodicNormalization
    (hp : p ≠ ⊤) (h2p : (2 : ℝ≥0∞) ≤ p) (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hphysical : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    {s : ℝ} (hΦ : HasOrderedTriangularSupport Φ s) (z : ℂ)
    (hprod : upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1 ≠ 0) :
    z ∈ periodicSpectrum hp (periodOnePotential (CoeffPair.exponentInclusion h2p
      (scaleUpperSource (orderedPeriodicNormalization Φ z) φ))) := by
  apply (source_mem_periodicSpectrum_orderedTriangular_iff hp h2p
    (scaleUpperSource (orderedPeriodicNormalization Φ z) φ)
    (scaleUpperCurve (orderedPeriodicNormalization Φ z) Φ)
    (physicalBase_scaleUpperSource _ φ Φ hphysical) (hΦ.scaleUpper _) z).mpr
  exact Or.inl (orderedPeriodicNormalization_product Φ z hprod)

/-- Exponent inclusion commutes with upper scaling and leaves the raw coefficients intact. -/
theorem scaleUpperSource_exponent {q : ℝ≥0∞} [Fact (1 ≤ q)] (hqp : q ≤ p)
    (c : ℂ) (φ : CoeffPair q) :
    CoeffPair.exponentInclusion hqp (scaleUpperSource c φ) =
      scaleUpperSource c (CoeffPair.exponentInclusion hqp φ) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · exact map_smul (Coeff.exponentInclusion hqp) c φ.fst
  · rfl

/-- At a nonreal parameter the normalization does not remove the upper component. -/
theorem orderedPeriodicNormalization_ne_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (him : z.im ≠ 0)
    (hprod : upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1 ≠ 0) :
    orderedPeriodicNormalization Φ z ≠ 0 := by
  have he : exp (-I*z) ≠ 1 := by
    intro h
    have hr := congrArg norm h
    rw [norm_exp, norm_one, Real.exp_eq_one_iff] at hr
    apply him
    simpa [mul_re] using hr
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr he))) hprod

/-- The normalized eigenvalue has a balanced source realization with an exact norm cost.
This is ready for a Fourier estimate and a lower bound on the interaction integrals. -/
theorem exists_balanced_source_orderedPeriodicNormalization
    (hp : p ≠ ⊤) (h2p : (2 : ℝ≥0∞) ≤ p) (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hphysical : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    {s : ℝ} (hΦ : HasOrderedTriangularSupport Φ s) (z : ℂ) (him : z.im ≠ 0)
    (hprod : upperInteractionPrimitive Φ z 1*lowerInteractionPrimitive Φ z 1 ≠ 0)
    (hfst : φ.fst ≠ 0) (hsnd : φ.snd ≠ 0) :
    ∃ ψ : CoeffPair p, ‖ψ.fst‖ = ‖ψ.snd‖ ∧
      z ∈ periodicSpectrum hp (periodOnePotential ψ) ∧
      ‖ψ‖ = (2 : ℝ)^(1/p.toReal)*Real.sqrt
        (‖orderedPeriodicNormalization Φ z‖ *
          ‖(CoeffPair.exponentInclusion h2p φ).fst‖ *
          ‖(CoeffPair.exponentInclusion h2p φ).snd‖) := by
  let κ := orderedPeriodicNormalization Φ z
  let χ := scaleUpperSource κ (CoeffPair.exponentInclusion h2p φ)
  have hκ : κ ≠ 0 := orderedPeriodicNormalization_ne_zero Φ z him hprod
  have ha : (CoeffPair.exponentInclusion h2p φ).fst ≠ 0 := by
    intro h
    exact hfst (Coeff.exponentInclusion_injective h2p (h.trans (map_zero _).symm))
  have hb : (CoeffPair.exponentInclusion h2p φ).snd ≠ 0 := by
    intro h
    exact hsnd (Coeff.exponentInclusion_injective h2p (h.trans (map_zero _).symm))
  have hχa : χ.fst ≠ 0 := smul_ne_zero hκ ha
  have hχb : χ.snd ≠ 0 := hb
  have hz : z ∈ periodicSpectrum hp (periodOnePotential χ) := by
    have h := source_mem_periodicSpectrum_orderedPeriodicNormalization hp h2p φ Φ hphysical hΦ z hprod
    rwa [scaleUpperSource_exponent] at h
  obtain ⟨c,h₁,h₂,hn,_⟩ := exists_source_balanced_diagonalPotential hp χ hχa hχb
  refine ⟨sourceDiagonalPotential c χ,h₁.trans h₂.symm,?_,?_⟩
  · rwa [sourcePeriodicSpectrum_diagonalPotential]
  · simpa only [χ,scaleUpperSource_fst,scaleUpperSource_snd,norm_smul] using hn

end NLS.ZakharovShabat

