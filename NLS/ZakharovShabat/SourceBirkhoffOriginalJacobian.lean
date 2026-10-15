import NLS.ZakharovShabat.SourceSection15Original
import NLS.ZakharovShabat.SourceGapWeightedEtaLemma16_1
import NLS.ZakharovShabat.SourceBirkhoffLemma16_3
import NLS.ZakharovShabat.SourceBirkhoffFourierSeries

/-!
# Jacobian and gradient estimates for the original map

The sequence-coordinate derivatives are the actual scalar derivatives.
Both finite-gap estimates retain the Section 15 root family and map.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
namespace SourceSection15OriginalData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
theorem gapSequence_fderiv (D : SourceSection15OriginalData hp hp1 W₀ W V s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (σ : ℂ) (hσ : ‖σ‖ ≤ 1) (n : ℤ) :
    fderiv ℂ (fun χ => sourceGapWeightedEtaSequence hp hp1 s σ χ n) ψ =
      fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s σ) ψ := by
  have he : (fun χ => sourceGapWeightedEtaSequence hp hp1 s σ χ n) =ᶠ[𝓝 ψ]
      sourceGapWeightedEtaCoordinate hp hp1 n s σ := by
    filter_upwards [D.previous.original_theta_common_domain.source_open.mem_nhds hψ] with χ hχ
    exact D.previous.gapWeighted_original_sequence_apply χ hχ σ hσ n
  exact he.fderiv_eq

theorem normalizedJacobian_hasSum (D : SourceSection15OriginalData hp hp1 W₀ W V s)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (h : CoeffPair p) :
    HasSum (fun n : ℤ =>
      ((fderiv ℂ (sourceBirkhoffX hp hp1 (-n) s) ψ) h) • sourceBirkhoffFreeXGradient p n -
      ((fderiv ℂ (sourceBirkhoffY hp hp1 (-n) s) ψ) h) • sourceBirkhoffFreeYGradient p n)
      (sourceBirkhoffNormalizedJacobian hp hp1 s ψ h) := by
  have hs := sourceBirkhoffFourierInverse_hasSum hp (sourceBirkhoffJacobian hp hp1 s ψ h)
  convert hs using 1
  · funext n
    rw [(D.complex.jacobian_coordinates ψ hψ h (-n)).1,
      (D.complex.jacobian_coordinates ψ hψ h (-n)).2]
  · rfl

theorem lemma16_1 [q.HolderConjugate p]
    (D : SourceSection15OriginalData hp hp1 W₀ W V s) (hq : q ≠ ⊤)
    (φ : realTypeSourceSubmodule p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (fun ψ => sourceGapWeightedEtaSequence hp hp1 s 1 ψ n) φ.val)+
      (2 : ℂ) • CoeffPair.inrCLM (lp.single q (-n) 1)‖) p ∧
    Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (fun ψ => sourceGapWeightedEtaSequence hp hp1 s (-1) ψ n) φ.val)+
      (2 : ℂ) • CoeffPair.inlCLM (lp.single q n 1)‖) p := by
  have h := D.complex.angular.gapWeightedEta_lemma16_1 hq V D.complex.source_open
    D.complex.source_subset φ (D.complex.real_subset φ.property) hfinite
  have hφW := D.complex.source_subset (D.complex.real_subset φ.property)
  simp_rw [gapSequence_fderiv D φ.val hφW 1 (by norm_num),
    gapSequence_fderiv D φ.val hφW (-1) (by norm_num)]
  exact h

theorem lemma16_2 [q.HolderConjugate p]
    (D : SourceSection15OriginalData hp hp1 W₀ W V s) (hq : q ≠ ⊤)
    (φ : realTypeSourceSubmodule p) (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ.val)-sourceBirkhoffFreeXGradient q n‖) p ∧
    Memℓp (fun n : ℤ => ‖CoeffPair.conjugateGradient hp hq
      (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val)-sourceBirkhoffFreeYGradient q n‖) p := by
  simp_rw [(D.complex.fderiv_coordinates _ φ.val (D.complex.real_subset φ.property)).1,
    (D.complex.fderiv_coordinates _ φ.val (D.complex.real_subset φ.property)).2]
  exact D.complex.angular.birkhoff_lemma16_2 hq V D.complex.source_open
    D.complex.source_subset φ (D.complex.real_subset φ.property) hfinite

end SourceSection15OriginalData

end NLS.ZakharovShabat
