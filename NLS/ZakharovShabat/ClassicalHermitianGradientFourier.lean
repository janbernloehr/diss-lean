import NLS.ComplexAnalysis.HermitianGradientFourierAssembly
import NLS.ZakharovShabat.ClassicalEndpointGradientFiniteSummability
import NLS.ZakharovShabat.SourceLemmaG5ReferenceAudit
import NLS.ZakharovShabat.ClassicalCharacteristicGradientRemainders

/-! # Actual full-matrix gradient Fourier coefficients for corrected G.5 -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ComplexAnalysis NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

-- Cache the standard normed structures for the nested operator spaces.
local instance : NormedAddCommGroup HermitianOperator := inferInstance
local instance : NormedSpace ℂ HermitianOperator := inferInstance
local instance : NormedAddCommGroup HermitianGradient := inferInstance
local instance : NormedSpace ℂ HermitianGradient := inferInstance

/-- Assemble the four matrix entries for one observation of the potential component. -/
def hermitianGradientComponentAssembly {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (F : (ℂ × ℂ) → ((ℂ × ℂ) →L[ℂ] ℂ) → ((ℂ × ℂ) →L[ℝ] ℂ) → Coeff q)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) : HermitianCoeff q :=
  hermitianFourierAssembly
    (F (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) P)
    (F (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) P)
    (F (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) P)
    (F (0,1) (ContinuousLinearMap.snd ℂ ℂ ℂ) P)

/-- All eight entries, with the factor i from the source statement. -/
def hermitianGradientObservationAssembly {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (F : (ℂ × ℂ) → ((ℂ × ℂ) →L[ℂ] ℂ) → ((ℂ × ℂ) →L[ℝ] ℂ) → Coeff q) :
    HermitianGradientCoeff q :=
  I • hermitianGradientFourierAssembly
    (hermitianGradientComponentAssembly F (ContinuousLinearMap.fst ℝ ℂ ℂ))
    (hermitianGradientComponentAssembly F (ContinuousLinearMap.snd ℝ ℂ ℂ))

theorem norm_hermitianGradientObservationAssembly_le {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (F : (ℂ × ℂ) → ((ℂ × ℂ) →L[ℂ] ℂ) → ((ℂ × ℂ) →L[ℝ] ℂ) → Coeff q) (K : ℝ)
    (hF : ∀ v, ‖v‖ ≤ 1 → ∀ L, ‖L‖ ≤ 1 → ∀ P, ‖P‖ ≤ 1 → ‖F v L P‖ ≤ K) :
    ‖hermitianGradientObservationAssembly F‖ ≤ 8*K := by
  have hc (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
      ‖hermitianGradientComponentAssembly F P‖ ≤ 4*K := by
    have h00 := hF (1,0) (by simp) _ (ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ) P hP
    have h10 := hF (1,0) (by simp) _ (ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ) P hP
    have h01 := hF (0,1) (by simp) _ (ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ) P hP
    have h11 := hF (0,1) (by simp) _ (ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ) P hP
    exact (norm_hermitianFourierAssembly_le _ _ _ _).trans (by linarith)
  rw [hermitianGradientObservationAssembly,norm_smul,norm_I,one_mul]
  exact (norm_hermitianGradientFourierAssembly_le _ _).trans
    (by linarith [hc _ (ContinuousLinearMap.norm_fst_le ℝ ℂ ℂ),
      hc _ (ContinuousLinearMap.norm_snd_le ℝ ℂ ℂ)])

/-- One potential component of the actual gradient matrix error. -/
def classicalGradientComponentOperator (φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (s : ℝ) : HermitianOperator :=
  hermitianColumns
    (P (classicalEndpointGradientRemainder φ z w (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) s),
     P (classicalEndpointGradientRemainder φ z w (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) s))
    (P (classicalEndpointGradientRemainder φ z w (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) s),
     P (classicalEndpointGradientRemainder φ z w (0,1) (ContinuousLinearMap.snd ℂ ℂ ℂ) s))

theorem continuous_classicalGradientComponentOperator (φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) : Continuous (classicalGradientComponentOperator φ z w P) := by
  change Continuous (fun s => classicalGradientComponentOperator φ z w P s)
  have hc (v : ℂ × ℂ) : Continuous (fun s =>
      (P (classicalEndpointGradientRemainder φ z w v (ContinuousLinearMap.fst ℂ ℂ ℂ) s),
       P (classicalEndpointGradientRemainder φ z w v (ContinuousLinearMap.snd ℂ ℂ ℂ) s))) :=
    (P.continuous.comp (contDiff_classicalEndpointGradientRemainder φ z w v _).continuous).prodMk
      (P.continuous.comp (contDiff_classicalEndpointGradientRemainder φ z w v _).continuous)
  simpa only [Function.comp_def,classicalGradientComponentOperator] using
    continuous_hermitianColumns.comp ((hc (1,0)).prodMk (hc (0,1)))

/-- i times the actual full gradient minus i times the actual free gradient at w. -/
def classicalHermitianGradientError (φ : Curve (ℂ × ℂ)) (z w : ℂ) (s : ℝ) : HermitianGradient :=
  I • hermitianGradientColumns
    (classicalGradientComponentOperator φ z w (ContinuousLinearMap.fst ℝ ℂ ℂ) s)
    (classicalGradientComponentOperator φ z w (ContinuousLinearMap.snd ℝ ℂ ℂ) s)

/-- Full gradient-valued Fourier coefficients, with the induced norm in both direction and matrix. -/
def classicalHermitianGradientFourierCoefficients {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) : HermitianGradientCoeff q :=
  hermitianGradientObservationAssembly (classicalEndpointGradientFourierCoefficients hq φ z w)

theorem classicalGradientComponentAssembly_integral {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (P : (ℂ × ℂ) →L[ℝ] ℂ) (k : ℤ) :
    hermitianGradientComponentAssembly (classicalEndpointGradientFourierCoefficients hq φ z w) P k =
      ∫ t in (0 : ℝ)..1, wave (-k) (2*t) • classicalGradientComponentOperator φ z w P t := by
  simp only [hermitianGradientComponentAssembly,hermitianFourierAssembly_apply,
    classicalEndpointGradientFourierCoefficients_apply]
  have hc (v : ℂ × ℂ) : Continuous (fun s =>
      (P (classicalEndpointGradientRemainder φ z w v (ContinuousLinearMap.fst ℂ ℂ ℂ) s),
       P (classicalEndpointGradientRemainder φ z w v (ContinuousLinearMap.snd ℂ ℂ ℂ) s))) :=
    (P.continuous.comp (contDiff_classicalEndpointGradientRemainder φ z w v _).continuous).prodMk
      (P.continuous.comp (contDiff_classicalEndpointGradientRemainder φ z w v _).continuous)
  exact hermitianColumns_intervalFourierCoefficient _ _ (hc (1,0)) (hc (0,1)) k

/-- Every assembled coefficient is the actual full-gradient Bochner Fourier integral. -/
theorem classicalHermitianGradientFourierCoefficients_apply {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (k : ℤ) :
    classicalHermitianGradientFourierCoefficients hq φ z w k =
      ∫ t in (0 : ℝ)..1, wave (-k) (2*t) • classicalHermitianGradientError φ z w t := by
  change I • hermitianGradientColumns _ _ = _
  rw [classicalGradientComponentAssembly_integral,classicalGradientComponentAssembly_integral,
    hermitianGradientColumns_intervalIntegral _ _
      (continuous_classicalGradientComponentOperator φ z w _)
      (continuous_classicalGradientComponentOperator φ z w _)]
  rw [← intervalIntegral.integral_smul]
  congr 1
  funext t
  exact smul_comm _ _ _

/-- The matrix of i times the actual gradient, evaluated on a potential direction. -/
def classicalHermitianGradientMatrix (φ : Curve (ℂ × ℂ)) (z : ℂ) (h : ℂ × ℂ) (s : ℝ) :
    HermitianOperator :=
  hermitianColumns
    (I*((classicalEndpointGradient φ z (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) s).1*h.1+
        (classicalEndpointGradient φ z (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) s).2*h.2),
     I*((classicalEndpointGradient φ z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) s).1*h.1+
        (classicalEndpointGradient φ z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) s).2*h.2))
    (I*((classicalEndpointGradient φ z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) s).1*h.1+
        (classicalEndpointGradient φ z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) s).2*h.2),
     I*((classicalEndpointGradient φ z (0,1) (ContinuousLinearMap.snd ℂ ℂ ℂ) s).1*h.1+
        (classicalEndpointGradient φ z (0,1) (ContinuousLinearMap.snd ℂ ℂ ℂ) s).2*h.2))

/-- The corrected free reference: upper minus component, lower plus component. -/
def classicalHermitianCorrectedFreeGradientMatrix (w : ℂ) (h : ℂ × ℂ) (s : ℝ) :
    HermitianOperator :=
  hermitianColumns (0,exp (I*w)*exp (-I*w*s)^2*h.2)
    (-exp (-I*w)*exp (I*w*s)^2*h.1,0)

/-- The full operator assembled above is exactly the error in corrected G.5. -/
theorem classicalHermitianGradientError_eq_correctedReference
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (h : ℂ × ℂ) (s : ℝ) :
    classicalHermitianGradientError φ z w s (hermitianPair h) =
      classicalHermitianGradientMatrix φ z h s-classicalHermitianCorrectedFreeGradientMatrix w h s := by
  simp only [classicalHermitianGradientError,smul_apply,hermitianGradientColumns_apply]
  ext x
  obtain ⟨v,rfl⟩ := hermitianPairEquiv.symm.surjective x
  apply hermitianPairEquiv.injective
  simp [classicalGradientComponentOperator,classicalHermitianGradientMatrix,
    classicalHermitianCorrectedFreeGradientMatrix,classicalEndpointGradientRemainder,
    classicalFreeEndpointGradient_fst_first,classicalFreeEndpointGradient_fst_second,
    classicalFreeEndpointGradient_snd_first,classicalFreeEndpointGradient_snd_second,
    hermitianColumns]
  constructor <;> ring_nf <;> simp [sub_eq_add_neg]

/-- The lattice reference has exactly the signed phase and waves in corrected G.5. -/
theorem classicalHermitianCorrectedFreeGradientMatrix_lattice
    (n : ℤ) (h : ℂ × ℂ) (s : Icc (0 : ℝ) 1) :
    classicalHermitianCorrectedFreeGradientMatrix ((Real.pi : ℂ)*n) h s =
      (-1 : ℂ)^n • hermitianColumns (0,wave (-(2*n)) s*h.2) (-wave (2*n) s*h.1,0) := by
  have hu := sourceG5_actual_i_zero_upper n s
  have hl := sourceG5_actual_i_zero_lower n s
  rw [classicalEndpointGradient_free,sourceG5_actual_i_free_upper] at hu
  rw [classicalEndpointGradient_free,sourceG5_actual_i_free_lower] at hl
  have hu' := congrArg Prod.fst hu
  have hl' := congrArg Prod.snd hl
  dsimp only at hu' hl'
  unfold classicalHermitianCorrectedFreeGradientMatrix
  rw [hu',hl',sourceG5LatticePhase_eq]
  ext x
  obtain ⟨v,rfl⟩ := hermitianPairEquiv.symm.surjective x
  apply hermitianPairEquiv.injective
  simp [hermitianColumns]
  constructor <;> ring

/-- At zero source, comparison with its own free frequency is exactly zero. -/
theorem classicalHermitianGradientError_zero (z : ℂ) (s : Icc (0 : ℝ) 1) :
    classicalHermitianGradientError 0 z z s = 0 := by
  simp [classicalHermitianGradientError,classicalGradientComponentOperator,
    classicalEndpointGradientRemainder,classicalEndpointGradient_free z _ _ s,
    hermitianColumns,hermitianGradientColumns,hermitianGradientLift,
    show (0,0) = (0 : ℂ × ℂ) from rfl]

/-- The zero-source assertion holds for the actual Fourier integrals at every frequency. -/
theorem classicalHermitianGradientFourierCoefficients_zero {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : 1 < q) (z : ℂ) : classicalHermitianGradientFourierCoefficients hq 0 z z = 0 := by
  apply lp.ext
  funext k
  rw [classicalHermitianGradientFourierCoefficients_apply]
  change (∫ t in (0 : ℝ)..1, wave (-k) (2*t) • classicalHermitianGradientError 0 z z t) = 0
  calc
    _ = ∫ _t in (0 : ℝ)..1, (0 : HermitianGradient) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
      change wave (-k) (2*t) • classicalHermitianGradientError 0 z z t = 0
      rw [classicalHermitianGradientError_zero z ⟨t,ht'⟩,smul_zero]
    _ = 0 := by simp

/-- Equal exponents give the same Fourier norm, without dependence on inequality proofs. -/
theorem norm_classicalHermitianGradientFourierCoefficients_congr
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : 1 < p) (hq : 1 < q)
    (hpq : p = q) (φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    ‖classicalHermitianGradientFourierCoefficients hp φ z w‖ =
      ‖classicalHermitianGradientFourierCoefficients hq φ z w‖ := by
  subst q
  rfl

end NLS.ZakharovShabat
