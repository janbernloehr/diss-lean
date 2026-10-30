import NLS.ZakharovShabat.SourceBirkhoffOriginalJacobian

/-! # The intermediate gradient estimates in the proof of Lemma 16.2

At real finite-gap sources the actual rectangular derivatives differ from
the normalized sum and difference of the unweighted eta derivatives by
outer lp sequences. The second estimate concerns y, with the same positive
sine orientation as equation (3.2). Both physical conjugate-gradient norms
and the actual sequence-coordinate evaluations are retained.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Both intermediate estimates of Lemma 16.2 in the full source operator norm. -/
theorem memlp_birkhoffXY_fderiv_sub_eta_finiteGap
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Memℓp (fun n : ℤ => fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val -
      (Real.sqrt 8 : ℂ)⁻¹ •
        (fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s 1) φ.val +
          fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s (-1)) φ.val)) p ∧
    Memℓp (fun n : ℤ => fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ.val -
      ((Real.sqrt 8 : ℂ)*I)⁻¹ •
        (fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s 1) φ.val -
          fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s (-1)) φ.val)) p := by
  have hxy := D.memlp_birkhoffXY_fderiv_sub_free_finiteGap W hW hWB φ hφ hfinite
  have hpη := D.memlp_gapWeightedEta_fderiv_sub_free_finiteGap_all_exponents W hW hWB φ hφ hfinite 1
  have hmη := D.memlp_gapWeightedEta_fderiv_sub_free_finiteGap_all_exponents W hW hWB φ hφ hfinite (-1)
  constructor
  · convert hxy.1.sub ((hpη.add hmη).const_smul (Real.sqrt 8 : ℂ)⁻¹) using 1
    funext n
    ext h
    simp only [sourceBirkhoffFreeXCotangent, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  · convert hxy.2.sub ((hpη.sub hmη).const_smul ((Real.sqrt 8 : ℂ)*I)⁻¹) using 1
    funext n
    ext h
    simp only [sourceBirkhoffFreeYCotangent, Pi.sub_apply, Pi.smul_apply,
      sub_apply, smul_apply, smul_eq_mul]
    ring

end SourceAngularEtaLocalCommonDomainData

namespace SourceSection15OriginalData
variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [q.HolderConjugate p]
  {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The printed intermediate gradient bounds, with y in the second estimate,
for the actual sequence entries and the physical Holder-conjugate pair norm. -/
theorem gradient_reduction_finiteGap
    (D : SourceSection15OriginalData hp hp1 W₀ W V s) (hq : q ≠ ⊤)
    (φ : realTypeSourceSubmodule p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    let X := fun n => CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ.val)
    let Y := fun n => CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val)
    let Z := fun σ n => CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (fun ψ => sourceGapWeightedEtaSequence hp hp1 s σ ψ n) φ.val)
    Memℓp (fun n : ℤ => ‖X n - (Real.sqrt 8 : ℂ)⁻¹ • (Z 1 n + Z (-1) n)‖) p ∧
      Memℓp (fun n : ℤ => ‖Y n - ((Real.sqrt 8 : ℂ)*I)⁻¹ • (Z 1 n - Z (-1) n)‖) p := by
  dsimp only
  have hφV := D.complex.real_subset φ.property
  have hφW := D.complex.source_subset hφV
  have he := D.complex.angular.memlp_birkhoffXY_fderiv_sub_eta_finiteGap
    V D.complex.source_open D.complex.source_subset φ hφV hfinite
  simp_rw [(D.complex.fderiv_coordinates _ φ.val hφV).1,
    (D.complex.fderiv_coordinates _ φ.val hφV).2,
    D.gapSequence_fderiv φ.val hφW 1 (by norm_num),
    D.gapSequence_fderiv φ.val hφW (-1) (by norm_num)]
  constructor
  · convert (CoeffPair.memlp_conjugateGradient hp hq _ he.1).norm using 1
    funext n
    congr 1
    exact (by simp only [← CoeffPair.conjugateGradientCLM_apply, map_sub, map_smul, map_add])
  · convert (CoeffPair.memlp_conjugateGradient hp hq _ he.2).norm using 1
    funext n
    congr 1
    exact (by simp only [← CoeffPair.conjugateGradientCLM_apply, map_sub, map_smul])

end SourceSection15OriginalData
end NLS.ZakharovShabat
