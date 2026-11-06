import NLS.ZakharovShabat.SourceRealBallCoreIdentity
import NLS.ZakharovShabat.SourceComplexBirkhoffMap
import NLS.ZakharovShabat.SourceBirkhoffLemma15_3
import NLS.Poisson.ComplexCanonicalCoordinates

/-! # Verified complex canonical differentials of the spectral Birkhoff map -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Poisson NLS.Birkhoff
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Complex coordinates have the actual full derivatives and the exact -i canonical bracket. -/
theorem complex_map_regular_canonical
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceSubmodule p) :
    ∃ Z T : ℤ → RegularSourceCotangent p,
      (∀ n, (Z n).toCotangent =
        fderiv ℂ (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).1 n) φ.val ∧
        (T n).toCotangent =
        fderiv ℂ (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).2 n) φ.val) ∧
      ∀ n m, (Z n).bivector (Z m) = 0 ∧
        (Z n).bivector (T m) = -I*(if n=m then 1 else 0) ∧ (T n).bivector (T m) = 0 := by
  obtain ⟨X,Y,hder,hbracket⟩ := D.lemma15_3 φ
  refine ⟨fun n => complexMinusCotangent (X n) (Y n),
    fun n => complexPlusCotangent (X n) (Y n),?_,
    complex_canonical_of_rectangular X Y hbracket⟩
  intro n
  have ha := (D.analytic φ.val (D.real_subset φ.property)).differentiableAt
  have hx : DifferentiableAt ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ.val :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).differentiableAt.comp φ.val
      ((ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).differentiableAt.comp φ.val ha)
  have hy : DifferentiableAt ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).differentiableAt.comp φ.val
      ((ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).differentiableAt.comp φ.val ha)
  have hdx : HasFDerivAt (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n)
      (X n).toCotangent φ.val := by rw [(hder n).1]; exact hx.hasFDerivAt
  have hdy : HasFDerivAt (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n)
      (Y n).toCotangent φ.val := by rw [(hder n).2]; exact hy.hasFDerivAt
  constructor
  · have hd := (hdx.sub (hdy.const_mul I)).const_mul complexCoordinateScale
    have hd' : HasFDerivAt
        (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).1 n)
        (complexMinusCotangent (X n) (Y n)).toCotangent φ.val := by
      have he : (complexMinusCotangent (X n) (Y n)).toCotangent =
          complexCoordinateScale • ((X n).toCotangent - I • (Y n).toCotangent) := by
        change complexCoordinateScale • (X n).toCotangent +
          (-complexCoordinateScale*I) • (Y n).toCotangent = _
        module
      rw [he]
      simpa only [sourceComplexBirkhoffMap,rectangularToComplex_fst] using! hd
    exact hd'.fderiv.symm
  · have hd := (hdx.add (hdy.const_mul I)).const_mul complexCoordinateScale
    have hd' : HasFDerivAt
        (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).2 n)
        (complexPlusCotangent (X n) (Y n)).toCotangent φ.val := by
      have he : (complexPlusCotangent (X n) (Y n)).toCotangent =
          complexCoordinateScale • ((X n).toCotangent + I • (Y n).toCotangent) := by
        change complexCoordinateScale • (X n).toCotangent +
          (complexCoordinateScale*I) • (Y n).toCotangent = _
        module
      rw [he]
      simpa only [sourceComplexBirkhoffMap,rectangularToComplex_snd] using! hd
    exact hd'.fderiv.symm
/-- The complex coordinate functions are analytic on the full constructed domain. -/
theorem complex_coordinates_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (n : ℤ) :
    AnalyticOnNhd ℂ (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).1 n) W ∧
    AnalyticOnNhd ℂ (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).2 n) W := by
  constructor <;> intro ψ hψ
  · exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).analyticAt _).comp
      (((ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).analyticAt _).comp
        (D.complex_map_analytic ψ hψ))
  · exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).analyticAt _).comp
      (((ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).analyticAt _).comp
        (D.complex_map_analytic ψ hψ))

/-- Canonicality holds on the whole complex ball core, not only the real subspace. -/
theorem complex_map_canonical_on_core
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : (2 : ℝ≥0∞) ≤ p)
    (ψ : CoeffPair p) (hψ : ψ ∈ sourceRealBallCore W) (n m : ℤ) :
    sourceBracket hp2 (fun φ => (sourceComplexBirkhoffMap hp hp1 s φ).1 n)
      (fun φ => (sourceComplexBirkhoffMap hp hp1 s φ).1 m) ψ = 0 ∧
    sourceBracket hp2 (fun φ => (sourceComplexBirkhoffMap hp hp1 s φ).1 n)
      (fun φ => (sourceComplexBirkhoffMap hp hp1 s φ).2 m) ψ = -I*(if n=m then 1 else 0) ∧
    sourceBracket hp2 (fun φ => (sourceComplexBirkhoffMap hp hp1 s φ).2 n)
      (fun φ => (sourceComplexBirkhoffMap hp hp1 s φ).2 m) ψ = 0 := by
  have hr (φ : realTypeSourceLocus p) :
      sourceBracket hp2 (fun χ => (sourceComplexBirkhoffMap hp hp1 s χ).1 n)
        (fun χ => (sourceComplexBirkhoffMap hp hp1 s χ).1 m) φ.val = 0 ∧
      sourceBracket hp2 (fun χ => (sourceComplexBirkhoffMap hp hp1 s χ).1 n)
        (fun χ => (sourceComplexBirkhoffMap hp hp1 s χ).2 m) φ.val = -I*(if n=m then 1 else 0) ∧
      sourceBracket hp2 (fun χ => (sourceComplexBirkhoffMap hp hp1 s χ).2 n)
        (fun χ => (sourceComplexBirkhoffMap hp hp1 s χ).2 m) φ.val = 0 := by
    obtain ⟨Z,T,hd,hb⟩ := D.complex_map_regular_canonical ⟨φ.val,φ.property⟩
    dsimp only [sourceBracket]
    rw [← (hd n).1,← (hd m).1,← (hd n).2,← (hd m).2]
    simpa only [← RegularSourceCotangent.bivector_eq_sourceBivector hp2] using hb n m
  have hnn := analyticOnNhd_sourceBracket hp2
    (D.complex_coordinates_analytic n).1 (D.complex_coordinates_analytic m).1
  have hnm := analyticOnNhd_sourceBracket hp2
    (D.complex_coordinates_analytic n).1 (D.complex_coordinates_analytic m).2
  have hmm := analyticOnNhd_sourceBracket hp2
    (D.complex_coordinates_analytic n).2 (D.complex_coordinates_analytic m).2
  exact ⟨eqOn_sourceRealBallCore_of_real_agreement hp D.real_subset _ (fun _ => 0)
      hnn analyticOnNhd_const (fun φ => (hr φ).1) hψ,
    eqOn_sourceRealBallCore_of_real_agreement hp D.real_subset _ (fun _ => -I*(if n=m then 1 else 0))
      hnm analyticOnNhd_const (fun φ => (hr φ).2.1) hψ,
    eqOn_sourceRealBallCore_of_real_agreement hp D.real_subset _ (fun _ => 0)
      hmm analyticOnNhd_const (fun φ => (hr φ).2.2) hψ⟩

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
