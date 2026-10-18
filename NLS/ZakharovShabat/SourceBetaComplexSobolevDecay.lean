import NLS.ZakharovShabat.SourceWeightedSpectralTermsComplex
import NLS.ZakharovShabat.SourceWeightedGapSequence
import NLS.SequenceSpaces.WeightedReciprocalDecay

/-! # Complex Sobolev beta decay

Weighted Hilbert majorants for the actual gaps and midpoint displacements give inverse-bracket decay of the original beta correction on one complex neighborhood.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A weighted majorant of the two actual spectral displacements controls beta at complex sources. -/
theorem sourceAngularBetaCorrection_complex_weighted_bound
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (ψ : CoeffPair 2) (G : Coeff 2)
    (hG : ∀ m : ℤ, (1+|(m:ℝ)|)*
      (‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ m‖+
        ‖sourceDirichletMidpointDisplacement (by simp) (by norm_num) ψ m‖) ≤ ‖G m‖)
    (C : ℝ) (hC : 0 ≤ C)
    (hbeta : ∀ n m : ℤ, m ≠ n →
      ‖sourceAngularBeta (by simp) (by norm_num) n m s ψ‖ ≤ C*
        (‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ m‖+
          ‖canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ m-
            sourceStandardRootMidpoint (by simp) (by norm_num) ψ m‖)/|((n-m:ℤ):ℝ)|)
    (n : ℤ) :
    (1+|(n:ℝ)|)*‖sourceAngularBetaCorrection (by simp) (by norm_num) n s ψ‖ ≤ 4*C*‖G‖ := by
  have hu (m : ℤ) :
      ‖sourceAngularBetaSeriesTerm (by simp) (by norm_num) n s ψ m‖ ≤
        C*‖G m‖/(1+|(m:ℝ)|)*‖Coeff.shift n (Coeff.puncturedLattice 2 (by norm_num)) m‖ := by
    rw [Coeff.norm_shift_puncturedLattice_apply]
    by_cases hm : m = n
    · simp only [sourceAngularBetaSeriesTerm,if_pos hm,norm_zero,mul_zero,le_refl]
    rw [sourceAngularBetaSeriesTerm,if_neg hm]
    have hg : ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ m‖+
        ‖sourceDirichletMidpointDisplacement (by simp) (by norm_num) ψ m‖ ≤ ‖G m‖/(1+|(m:ℝ)|) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hG m)
    have hb := hbeta n m hm
    rw [← sourceDirichletMidpointDisplacement_apply] at hb
    calc
      _ ≤ C*(‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ m‖+
          ‖sourceDirichletMidpointDisplacement (by simp) (by norm_num) ψ m‖)/|((n-m:ℤ):ℝ)| := hb
      _ ≤ C*(‖G m‖/(1+|(m:ℝ)|))/|((n-m:ℤ):ℝ)| := by gcongr
      _ = _ := by rw [if_neg hm,Int.cast_sub,abs_sub_comm]; push_cast; ring
  obtain ⟨hs,hb⟩ := Coeff.summable_norm_reciprocal_of_weighted_hilbert G _ n C hC hu
  exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs) (by positivity)).trans hb

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The original beta corrections decay on a complex normalized first-order Sobolev neighborhood. -/
theorem exists_local_normalizedSobolevBetaCorrection_decay (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        (1+|(n:ℝ)|)*‖sourceAngularBetaCorrection (by simp) (by norm_num) n s
          (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ)‖ ≤ K := by
  let w := SpectralWeight.sobolev 1 (by norm_num)
  let φu : realTypeSourceSubmodule 2 :=
    ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Vs,hVs,hφs,_,M,hM,hs⟩ := D.exists_local_normalizedWeightedSpectralTerms_bound w φ
  obtain ⟨Vb,hVb,hφb,_,C,hC,hbeta⟩ := D.angular.beta_bound φu.val (D.source_subset (D.real_subset φu.property))
  let L := normalizedWeightedSourceCLM (p := 2) w
  let S := (normalizedWeightedPeriodOne (p := 2) w).toContinuousLinearMap
  have hSL : ∀ b, weightedBaseToPair w (S b) = periodOnePotential (L b) :=
    fun b => weightedBaseToPair_normalizedWeightedPeriodOne w b
  obtain ⟨Vg,hVg,hφg,G,hG,hgap⟩ := exists_local_sourceWeightedGapSequence_bound (by simp) (by norm_num) w L S hSL φ.val
  let U := (Vs ∩ Vg) ∩ normalizedWeightedSource w ⁻¹' Vb
  have hU : IsOpen U := (hVs.inter hVg).inter (hVb.preimage (continuous_normalizedWeightedSource w))
  refine ⟨U,hU,⟨⟨hφs,hφg⟩,hφb⟩,4*C*(G+M),by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨A,B,hA,_,hnA,_⟩ := hs ψ hψ.1.1
  let g := sourceWeightedGapSequence (by simp) (by norm_num) w L S hSL ψ
  let H := Coeff.magnitude g+Coeff.magnitude A
  have hgc (m : ℤ) : g m = (w (2*m):ℂ)*sourcePeriodicGapDisplacement (by simp) (by norm_num)
      (normalizedWeightedSource w ψ) m := rfl
  have hHc (m : ℤ) : ‖H m‖ = ‖g m‖+‖A m‖ := by
    simp only [H,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ ‖g m‖+‖A m‖)]
  have hHnorm : ‖H‖ ≤ G+M := by
    have hh := norm_add_le (Coeff.magnitude g) (Coeff.magnitude A)
    simp only [Coeff.norm_magnitude] at hh
    exact hh.trans (add_le_add (hgap ψ hψ.1.2) hnA)
  have hmajor (m : ℤ) : (1+|(m:ℝ)|)*
      (‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (normalizedWeightedSource w ψ) m‖+
        ‖sourceDirichletMidpointDisplacement (by simp) (by norm_num) (normalizedWeightedSource w ψ) m‖) ≤ ‖H m‖ := by
    rw [hHc,hgc,hA,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (w.positive _).le,← mul_add]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simp only [w,SpectralWeight.sobolev_apply,Weight.sobolev_apply,Real.rpow_one,
      Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [abs_nonneg (m:ℝ)]
  exact (sourceAngularBetaCorrection_complex_weighted_bound s _ H hmajor C hC.le (hbeta _ hψ.2) n).trans
    (mul_le_mul_of_nonneg_left hHnorm (by positivity))

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
