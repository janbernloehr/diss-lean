import NLS.ZakharovShabat.SourceHamiltonianFiniteGapDerivative
import NLS.ZakharovShabat.SourceSecondMomentFrequencyTheorem20_4
import NLS.ZakharovShabat.SourceFiniteGapDensity
import NLS.SequenceSpaces.HilbertScalarGradient

/-! # The Hamiltonian gradient at all actual real FL⁴ sources

Physical finite-gap derivative identities transfer across source exponents.
Density in the original FL⁴ norm and continuity of the Banach derivative
then identify every Hamiltonian coordinate derivative with the actual
renormalized frequency, without any finite-gap assumption.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4:ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W W₀ B X Y P : Set (CoeffPair 4)}
variable {t u : (k : ℤ) → CoeffPair 4 → DeletedCoeff 4 k}

/-- Every coordinate of the actual Hamiltonian's action derivative equals
the established renormalized frequency at every real FL⁴ source. -/
theorem sourceHamiltonian_fderiv_real
    (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t)
    (C : SourceAbelianMomentAtlas (by simp) (by norm_num) Y u)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P u)
    (hP : IsOpen P) (hrealP : realTypeSourceLocus 4 ⊆ P)
    (H : Coeff 2 → ℂ) (V : Set (Coeff 2)) (hH : AnalyticOnNhd ℂ H V)
    (hcenter : ∀ ψ : realTypeSourceSubmodule 4,
      sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val ∈ V)
    (hrec : ∀ ψ : realTypeSourceSubmodule 4,
      H (sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val) = A.renormalizedHamiltonian ψ.val)
    (φ : realTypeSourceSubmodule 4) (n : ℤ) :
    fderiv ℂ H (sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val) (lp.single 2 n 1) =
      C.renormalizedFrequency n φ.val := by
  obtain ⟨Y₂,P₂,_,_,_,_,u₂,hs₂,⟨C₂⟩⟩ :=
    exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨U,_,_,hrealU,_,_,hfreq,_⟩ := C.exists_analytic_renormalizedFrequency hs hP hrealP
  let I := fun ψ : realTypeSourceSubmodule 4 => sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val
  have hder : ContinuousOn (fun ψ : realTypeSourceSubmodule 4 => fderiv ℂ H (I ψ) (lp.single 2 n 1)) univ := by
    apply Continuous.continuousOn
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((hH.fderiv (I ψ) (hcenter ψ)).continuousAt.clm_apply continuousAt_const).comp
      ((D.actionSequence_analytic ψ.val (D.real_subset ψ.property)).continuousAt.comp continuous_subtype_val.continuousAt)
  have hval : ContinuousOn (fun ψ : realTypeSourceSubmodule 4 => C.renormalizedFrequency n ψ.val) univ :=
    (hfreq n).continuousOn.comp continuous_subtype_val.continuousOn (fun ψ _ => hrealU ψ.property)
  apply sub_eq_zero.mp
  apply eq_of_continuousOn_of_sourceFiniteGap (by simp) (by norm_num) isOpen_univ
    (hder.sub hval) 0 _ φ (mem_univ φ)
  intro ψ _ hf
  obtain ⟨χ,hcoeff,hχ,_⟩ := sourceFiniteGap_exists_hilbert_mass_model (by simp) (by norm_num) ψ hf
  have he : realTypeSourceExponentInclusion (by norm_num : (2:ℝ≥0∞) ≤ 4) χ = ψ := by
    apply Subtype.ext
    apply (CoeffPair.toMax 4).injective
    apply Prod.ext
    · ext k; exact (hcoeff k).1
    · ext k; exact (hcoeff k).2
  have hd := sourceHamiltonian_fderiv_finiteGap_hilbert A D C₂ hs₂.toSourcePsiNormalizedComplexExtension
    H V hH hcenter hrec χ hχ n
  have hc := C.renormalizedFrequency_real_eq_of_coefficients C₂ hs.toSourcePsiIsolatingComplexExtension
    hs₂.toSourcePsiIsolatingComplexExtension ψ χ hcoeff n
  apply sub_eq_zero.mpr
  exact (show fderiv ℂ H (I ψ) (lp.single 2 n 1) = C₂.renormalizedFrequency n χ.val from
    by simpa only [he] using hd).trans hc.symm

/-- The full differential is the absolutely convergent frequency pairing
on every complex Hilbert direction, including infinite-support directions. -/
theorem sourceHamiltonian_fderiv_real_series
    (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t)
    (C : SourceAbelianMomentAtlas (by simp) (by norm_num) Y u)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P u)
    (hP : IsOpen P) (hrealP : realTypeSourceLocus 4 ⊆ P)
    (H : Coeff 2 → ℂ) (V : Set (Coeff 2)) (hH : AnalyticOnNhd ℂ H V)
    (hcenter : ∀ ψ : realTypeSourceSubmodule 4,
      sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val ∈ V)
    (hrec : ∀ ψ : realTypeSourceSubmodule 4,
      H (sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val) = A.renormalizedHamiltonian ψ.val)
    (φ : realTypeSourceSubmodule 4) (J : Coeff 2) :
    Summable (fun n : ℤ => ‖C.renormalizedFrequency n φ.val * J n‖) ∧
      fderiv ℂ H (sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val) J =
        ∑' n : ℤ, C.renormalizedFrequency n φ.val * J n := by
  let b := sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val
  have he (n : ℤ) : Coeff.scalarGradient H b n = C.renormalizedFrequency n φ.val := by
    rw [Coeff.scalarGradient_apply]
    exact sourceHamiltonian_fderiv_real A D C hs hP hrealP H V hH hcenter hrec φ n
  refine ⟨?_,?_⟩
  · simpa only [he] using Coeff.summable_norm_dualPairing (Coeff.scalarGradient H b) J
  · rw [Coeff.fderiv_eq_dualPairing_scalarGradient,Coeff.dualPairing_apply]
    exact tsum_congr (fun n => congrArg (fun z : ℂ => z * J n) (he n))

end NLS.ZakharovShabat
