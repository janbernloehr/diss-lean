import NLS.ZakharovShabat.ClassicalReciprocalScaling
import NLS.ZakharovShabat.SourceMidpointReflection
import NLS.ZakharovShabat.PeriodicSpectralDataUniqueness
import NLS.ZakharovShabat.SourceCanonicalRootProduct

/-! # Reciprocal scaling and every physical source phase rotation

Finite Fourier synthesis identifies the scaling with the physical ODE gauge.
Continuity extends its discriminant identity to every complex finite source
exponent p>1, including the original L2 domain. Intrinsic algebraic spectral
data then fix all signed endpoint labels and the literal canonical root.
-/
noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceReciprocalScaling (c : ℂ) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    (((c • ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).prod
      (c⁻¹ • ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))).comp
        (CoeffPair.toMax p).toContinuousLinearMap)

@[simp] theorem sourceReciprocalScaling_fst (c : ℂ) (φ : CoeffPair p) :
    (sourceReciprocalScaling c φ).fst = c • φ.fst := rfl

@[simp] theorem sourceReciprocalScaling_snd (c : ℂ) (φ : CoeffPair p) :
    (sourceReciprocalScaling c φ).snd = c⁻¹ • φ.snd := rfl

@[simp] theorem sourceReciprocalScaling_ofFinsupp (c : ℂ)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    sourceReciprocalScaling c (CoeffPair.ofFinsupp (p := p) a) =
      CoeffPair.ofFinsupp (c • a.1,c⁻¹ • a.2) := by
  apply (CoeffPair.toMax p).injective
  change (c • Coeff.ofFinsupp a.1,c⁻¹ • Coeff.ofFinsupp a.2) =
    (Coeff.ofFinsupp (c • a.1),Coeff.ofFinsupp (c⁻¹ • a.2))
  simp only [map_smul]

private theorem polynomial_scaling (c : ℂ) (a : ℤ →₀ ℂ) (t : ℝ) :
    polynomial (c • a) t = c*polynomial a t := by
  unfold polynomial
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.sum,Finset.mul_sum,mul_assoc]

theorem finiteSourceCurve_reciprocalScaling (c : ℂ)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    finiteSourceCurve (c • a.1,c⁻¹ • a.2) =
      classicalReciprocalScaling c (finiteSourceCurve a) := by
  ext t <;> simp only [finiteSourceCurve,BoundaryCondition.periodOnePair,
    ContinuousMap.coe_mk,classicalReciprocalScaling_apply,polynomial_scaling]

theorem sourceDiscriminant_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential (sourceReciprocalScaling c φ)) z =
      canonicalDiscriminant hp (periodOnePotential φ) z := by
  have hcont : Continuous (fun ψ : CoeffPair p =>
      canonicalDiscriminant hp (periodOnePotential ψ) z) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
      (z,ψ) (mem_univ _)).comp (f := fun χ : CoeffPair p => (z,χ))
      (analyticAt_const.prod analyticAt_id)).continuousAt
  have he := sourceDiscriminant_unique_continuous hp hp1 z
    (fun ψ => canonicalDiscriminant hp
      (periodOnePotential (sourceReciprocalScaling c ψ)) z)
    (hcont.comp (sourceReciprocalScaling c).continuous) (by
      intro a
      rw [sourceReciprocalScaling_ofFinsupp,sourceDiscriminant_finite_eq_classical,
        finiteSourceCurve_reciprocalScaling,classicalDiscriminant_reciprocalScaling c hc])
  exact congrFun he φ

theorem sourceDiscriminant_deriv_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) (z : ℂ) :
    deriv (canonicalDiscriminant hp (periodOnePotential (sourceReciprocalScaling c φ))) z =
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) z :=
  congrArg (fun f : ℂ → ℂ => deriv f z)
    (funext (sourceDiscriminant_reciprocalScaling hp hp1 c hc φ))

theorem sourceDiscriminantCotangent_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) (z : ℂ) :
    sourceDiscriminantCotangent hp z φ =
      (sourceDiscriminantCotangent hp z (sourceReciprocalScaling c φ)).comp
        (sourceReciprocalScaling c) :=
  sourceDiscriminantCotangent_of_linear_symmetry hp hp1 (sourceReciprocalScaling c) z z
    (fun ψ => sourceDiscriminant_reciprocalScaling hp hp1 c hc ψ z) φ

theorem sourcePeriodicSpectrum_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) :
    periodicSpectrum hp (periodOnePotential (sourceReciprocalScaling c φ)) =
      periodicSpectrum hp (periodOnePotential φ) := by
  ext z
  rw [← canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem _) z,
    sourceDiscriminant_reciprocalScaling hp hp1 c hc φ z,
    canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem _) z]

theorem sourcePeriodicMultiplicity_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) (z : ℂ) :
    periodicAlgebraicMultiplicity hp (periodOnePotential (sourceReciprocalScaling c φ)) z =
      periodicAlgebraicMultiplicity hp (periodOnePotential φ) z := by
  have he : (fun w : ℂ =>
      (canonicalDiscriminant hp (periodOnePotential (sourceReciprocalScaling c φ)) w)^2-4) =
      (fun w : ℂ => (canonicalDiscriminant hp (periodOnePotential φ) w)^2-4) := by
    funext w
    rw [sourceDiscriminant_reciprocalScaling hp hp1 c hc φ w]
  have ho := congrArg (fun f : ℂ → ℂ => analyticOrderAt f z) he
  rw [analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem _) z,
    analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem _) z] at ho
  exact_mod_cast ho

theorem sourceCanonicalPeriodicEndpoints_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceReciprocalScaling c φ)) (periodOnePotential_mem _) =
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential (sourceReciprocalScaling c φ)) (periodOnePotential_mem _) =
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) :=
  canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1 _ _
    (periodOnePotential_mem _) (periodOnePotential_mem _)
    (sourcePeriodicSpectrum_reciprocalScaling hp hp1 c hc φ)
    (sourcePeriodicMultiplicity_reciprocalScaling hp hp1 c hc φ)

theorem sourceStandardRoot_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    sourceStandardRoot hp hp1 (sourceReciprocalScaling c φ) n z =
      sourceStandardRoot hp hp1 φ n z := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_reciprocalScaling hp hp1 c hc φ
  unfold sourceStandardRoot canonicalPeriodicMidpoint canonicalPeriodicGap
  rw [hl,hr]

theorem sourceCanonicalRoot_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) (z : ℂ) :
    sourceCanonicalRoot hp hp1 (sourceReciprocalScaling c φ) z =
      sourceCanonicalRoot hp hp1 φ z := by
  simp only [sourceCanonicalRoot,sourceStandardRootPairedProduct,
    sourceStandardRootPairedFactor,sourceStandardRoot_reciprocalScaling hp hp1 c hc]

end NLS.ZakharovShabat
