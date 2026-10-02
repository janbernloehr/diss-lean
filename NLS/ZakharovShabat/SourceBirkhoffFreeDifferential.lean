import NLS.ZakharovShabat.SourceFreeSpectralDifferentials
import NLS.ZakharovShabat.SourceGapWeightedEtaFiniteGapDifferential
import NLS.ZakharovShabat.SourceBirkhoffFixedFamilyAnalytic

/-! # The Birkhoff differential at the free potential

The normalized action root and beta phase equal one at zero. The
vanishing gap-weighted factor eliminates their derivatives, leaving
an explicit Fourier-coordinate formula for the full differential.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp] theorem sourceNormalizedActionRoot_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourceNormalizedActionRoot hp hp1 n (0 : CoeffPair p) = 1 := by
  simp [sourceNormalizedActionRoot, sourceNormalizedActionComplexExtension_zero_source]

@[simp] theorem sourceAngularBetaCorrection_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) :
    sourceAngularBetaCorrection hp hp1 n s 0 = 0 := by
  have hb (m : ℤ) : sourceAngularBeta hp hp1 n m s 0 = 0 :=
    sourceAngularBeta_eq_zero_of_real_collapsed_gap hp hp1 n m s 0 (by simp)
      (by simpa only [sourcePeriodicGapDisplacement_apply, map_zero] using
        canonicalPeriodicGap_zero hp hp1 m)
  simp [sourceAngularBetaCorrection, sourceAngularBetaSeriesTerm, hb]

@[simp] theorem sourceGapWeightedEtaCoordinate_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (sign : ℂ) :
    sourceGapWeightedEtaCoordinate hp hp1 n s sign 0 = 0 := by
  simp only [sourceGapWeightedEtaCoordinate, sourceDirichletEtaSineNumerator,
    canonicalPeriodOneBoundaryRoots_zero, map_zero, canonicalPeriodicMidpoint_zero,
    sourceAntiDiscriminantCandidate_zero, zero_div, sub_self, mul_zero, add_zero, zero_mul]

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- At zero, the normalization and phase do not change the differential. -/
theorem birkhoffWeighted_fderiv_zero
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B) (h0 : (0 : CoeffPair p) ∈ W)
    (n : ℤ) (sign : ℂ) :
    fderiv ℂ (sourceBirkhoffWeightedCoordinate hp hp1 n s sign) 0 =
      fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) 0 := by
  obtain ⟨A,_,h0A,hξ,_⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 0 (by simp)
  have hz := D.gapWeightedEta_analyticAt_of_realType W hW hWB 0 h0 (by simp) n sign
  have he : AnalyticAt ℂ (fun ψ => exp (sign*I*sourceAngularBetaCorrection hp hp1 n s ψ)) 0 :=
    (analyticAt_const.mul (D.beta_series.analytic_correction n 0 (hWB h0))).cexp'
  have hd := (((hξ n 0 h0A).differentiableAt.hasFDerivAt.fun_mul
    hz.differentiableAt.hasFDerivAt).fun_mul he.differentiableAt.hasFDerivAt).fderiv
  change fderiv ℂ (sourceBirkhoffWeightedCoordinate hp hp1 n s sign) 0 = _ at hd
  rw [hd]
  ext h
  simp [add_apply, smul_apply, smul_eq_mul]

end SourceAngularEtaLocalCommonDomainData

namespace SourceAngularEtaLocalCommonDomainData
variable {W₀ B : Set (CoeffPair 2)}
  {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Both signed eta differentials at zero, including their frequency
reflection and exact factors. -/
theorem gapWeightedEta_fderiv_zero
    (D : SourceAngularEtaLocalCommonDomainData (p := 2) (by simp) (by norm_num) W₀ B s)
    (W : Set (CoeffPair 2)) (hW : IsOpen W) (hWB : W ⊆ B) (h0 : (0 : CoeffPair 2) ∈ W)
    (n : ℤ) (sign : ℂ) (h : CoeffPair 2) :
    (fderiv ℂ (sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s sign) 0) h =
      (sign-1)*h.fst (-n) - (sign+1)*h.snd n := by
  have hd := D.gapWeightedEta_fderiv_closed W hW hWB ⟨0,by simp⟩ h0 n
    (by simpa only [map_zero] using (canonicalPeriodicGap_zero (p := 2) (by simp) (by norm_num) n)) sign
  have hc : cos ((Real.pi : ℂ)*n) ≠ 0 := by
    intro hz
    have hn := norm_cos_freeCenter n
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  have hanti : sourceAntiDiscriminantCandidate (p := 2) (by simp) (by norm_num) 0 = (fun _ => 0) :=
    funext (sourceAntiDiscriminantCandidate_zero (by simp) (by norm_num))
  rw [hd]
  dsimp only [sourceGapWeightedEtaClosedCotangent]
  simp only [canonicalPeriodOneBoundaryRoots_zero, sourceStandardRootOmittedProduct_zero_center,
    hanti, deriv_const, smul_apply, add_apply, smul_eq_mul,
    fderiv_canonicalPeriodOneBoundaryRoot_zero, fderiv_canonicalPeriodicMidpoint_zero,
    sourceAntiDiscriminantCotangent_zero,
    BoundaryCondition.extensionSign, zero_mul, add_zero, sub_zero]
  field_simp
  ring_nf
  simp [I_sq, sub_eq_add_neg]

/-- The free rectangular derivatives on the entire complex Hilbert source. -/
theorem birkhoffXY_fderiv_zero_hilbert
    (D : SourceAngularEtaLocalCommonDomainData (p := 2) (by simp) (by norm_num) W₀ B s)
    (W : Set (CoeffPair 2)) (hW : IsOpen W) (hWB : W ⊆ B) (h0 : (0 : CoeffPair 2) ∈ W)
    (n : ℤ) (h : CoeffPair 2) :
    (fderiv ℂ (sourceBirkhoffX (by simp) (by norm_num) n s) 0) h =
      -(h.fst (-n)+h.snd n)/(Real.sqrt 2 : ℂ) ∧
    (fderiv ℂ (sourceBirkhoffY (by simp) (by norm_num) n s) 0) h =
      (h.fst (-n)-h.snd n)/((Real.sqrt 2 : ℂ)*I) := by
  obtain ⟨A,_,h0A,hξ,_⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic
    (p := 2) (by simp) (by norm_num) 0 (by simp)
  have ha (sign : ℂ) := (analyticAt_sourceBirkhoffWeightedCoordinate (by simp) (by norm_num)
    n s sign 0 (hξ n 0 h0A)
    (D.gapWeightedEta_analyticAt_of_realType W hW hWB 0 h0 (by simp) n sign)
    (D.beta_series.analytic_correction n 0 (hWB h0))).differentiableAt.hasFDerivAt
  have hx := (((ha 1).add (ha (-1))).mul_const (Real.sqrt 8 : ℂ)⁻¹).fderiv
  have hy := (((ha 1).sub (ha (-1))).mul_const ((Real.sqrt 8 : ℂ)*I)⁻¹).fderiv
  have hs : (Real.sqrt 8 : ℂ) = 2*(Real.sqrt 2 : ℂ) := by
    have hr : Real.sqrt 8 = 2*Real.sqrt 2 := by
      rw [show (8 : ℝ) = 4*2 by norm_num, Real.sqrt_mul (by norm_num)]
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    exact_mod_cast hr
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  change fderiv ℂ (sourceBirkhoffX (by simp) (by norm_num) n s) 0 = _ at hx
  change fderiv ℂ (sourceBirkhoffY (by simp) (by norm_num) n s) 0 = _ at hy
  rw [hx,hy]
  simp only [smul_apply, add_apply, sub_apply, smul_eq_mul,
    D.birkhoffWeighted_fderiv_zero W hW hWB h0,
    D.gapWeightedEta_fderiv_zero W hW hWB h0, hs]
  constructor <;> field_simp <;> ring

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
