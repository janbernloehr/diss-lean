import NLS.ZakharovShabat.SourceWeightedSpectralTermsComplex
import NLS.ZakharovShabat.SourceAngularUniformAnnulusPrimitive
import NLS.ZakharovShabat.SourceAngularEtaRemainderGlobal
import NLS.ZakharovShabat.SourceWeightedGapSequence

/-! # Complex analyticity and weighted bounds for eta remainders

The retained original family has one common domain of scalar analyticity. The actual gap and midpoint bounds also preserve every native spectral weight.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
include D

/-- The retained original family has all actual eta remainders analytic on one complex neighborhood. -/
theorem exists_local_etaRemainder_allIndices_analytic (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ W ∧
      ∀ n : ℤ, AnalyticOnNhd ℂ (sourceAngularEtaRemainder hp hp1 n s) U := by
  obtain ⟨a,ha,_,_,_,_,hball,_⟩ := D.angular.psi.isolation φ
  let O := W ∩ ball φ.val a
  have hO : IsOpen O := D.source_open.inter isOpen_ball
  have hφO : φ.val ∈ O := ⟨D.real_subset φ.property,mem_ball_self ha⟩
  have hOW₀ : O ⊆ W₀ := fun _ h => hball h.2
  have hOB : O ⊆ B := fun _ h => D.source_subset h.1
  obtain ⟨V,hV,hφV,hVO,hcharts⟩ :=
    D.angular.psi.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives_allIndices
      O hO hOW₀ (fun ψ hψ => D.angular.symmetric_analytic ψ (hOB hψ)) φ.val hφO φ.property
  refine ⟨V,hV,hφV,(fun _ h => (hVO h).1),?_⟩
  intro n
  obtain ⟨c,T,r,R,z₀,C⟩ := hcharts n
  exact C.analyticOnNhd_etaRemainder ((r+R)/2)
    (by linarith [C.inner_lt_outer]) (by linarith [C.inner_lt_outer])
    ((D.angular.roots_analytic .dirichlet n).mono (hVO.trans hOB))

/-- The actual eta remainder preserves the native spectral weight locally at complex sources. -/
theorem exists_local_normalizedWeightedEtaRemainder_bound
    (w : SpectralWeight) (φ : realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      (∀ ψ ∈ U, normalizedWeightedSource w ψ ∈ W) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U,
        Memℓp (fun n => (w (2*n):ℂ)*sourceAngularEtaRemainder hp hp1 n s
          (normalizedWeightedSource w ψ)) p ∧
        ‖Coeff.ofFunctionOrZero p (fun n => (w (2*n):ℂ)*sourceAngularEtaRemainder hp hp1 n s
          (normalizedWeightedSource w ψ))‖ ≤ M := by
  let φu : realTypeSourceSubmodule p :=
    ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Vr,hVr,hφr,_,C,hC,hr⟩ := D.exists_local_uniform_etaRemainder_gap_bound φu
  obtain ⟨Vs,hVs,hφs,hVsW,M₀,hM₀,hs⟩ := D.exists_local_normalizedWeightedSpectralTerms_bound w φ
  let L := normalizedWeightedSourceCLM (p := p) w
  let S := (normalizedWeightedPeriodOne (p := p) w).toContinuousLinearMap
  have hSL : ∀ b, weightedBaseToPair w (S b) = periodOnePotential (L b) :=
    fun b => weightedBaseToPair_normalizedWeightedPeriodOne w b
  obtain ⟨Vg,hVg,hφg,G,hG,hgap⟩ := exists_local_sourceWeightedGapSequence_bound hp hp1 w L S hSL φ.val
  let U := (Vs ∩ Vg) ∩ normalizedWeightedSource w ⁻¹' Vr
  have hU : IsOpen U := (hVs.inter hVg).inter (hVr.preimage (continuous_normalizedWeightedSource w))
  refine ⟨U,hU,⟨⟨hφs,hφg⟩,hφr⟩,(fun ψ hψ => hVsW ψ hψ.1.1),C*(M₀+G),by positivity,?_⟩
  intro ψ hψ
  obtain ⟨A,B,hA,_,hnA,_⟩ := hs ψ hψ.1.1
  let g := sourceWeightedGapSequence hp hp1 w L S hSL ψ
  have hgc (n : ℤ) : g n = (w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 (normalizedWeightedSource w ψ) n := rfl
  have hbound (n : ℤ) :
      ‖(w (2*n):ℂ)*sourceAngularEtaRemainder hp hp1 n s (normalizedWeightedSource w ψ)‖ ≤
        C*(‖A n‖+‖g n‖) := by
    rw [hA,hgc,norm_mul,norm_mul,norm_mul]
    have h := hr _ hψ.2 n
    rw [← sourceDirichletMidpointDisplacement_apply] at h
    have hg := norm_nonneg (sourcePeriodicGapDisplacement hp hp1 (normalizedWeightedSource w ψ) n)
    have h' : ‖sourceAngularEtaRemainder hp hp1 n s (normalizedWeightedSource w ψ)‖ ≤
        C*(‖sourceDirichletMidpointDisplacement hp hp1 (normalizedWeightedSource w ψ) n‖+
          ‖sourcePeriodicGapDisplacement hp hp1 (normalizedWeightedSource w ψ) n‖) :=
      h.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
    exact (mul_le_mul_of_nonneg_left h' (norm_nonneg _)).trans_eq (by ring)
  obtain ⟨hm,hn⟩ := Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound _ A g C hC hbound
  exact ⟨hm,hn.trans (mul_le_mul_of_nonneg_left (add_le_add hnA (hgap ψ hψ.1.2)) hC)⟩

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
