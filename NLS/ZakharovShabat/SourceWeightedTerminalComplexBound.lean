import NLS.ZakharovShabat.SourceWeightedEtaComplexAnalytic
import NLS.ZakharovShabat.SourceEtaRemainderLocalGapBound
import NLS.ZakharovShabat.SourceBirkhoffSpectralTerminal

/-! # Complex bounds for the literal terminal

Removing the exact eta-remainder phase transfers the native weighted bound to the literal terminal coordinate.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
include D

/-- One complex neighborhood bounds every actual eta remainder. -/
theorem exists_local_uniform_etaRemainder_bound (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ W ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        ‖sourceAngularEtaRemainder hp hp1 n s ψ‖ ≤ A := by
  obtain ⟨Ve,hVe,hφe,hVeW,C,hC,he⟩ := D.exists_local_uniform_etaRemainder_gap_bound φ
  obtain ⟨Vb,hVb,hφb,_,G,A,hG,_,hb⟩ := D.angular.exists_local_uniform_betaCorrection_bound
    φ.val (D.source_subset (D.real_subset φ.property))
  refine ⟨Ve ∩ Vb,hVe.inter hVb,⟨hφe,hφb⟩,
    (fun _ hψ => hVeW hψ.1),C*G,mul_nonneg hC hG,?_⟩
  intro ψ hψ n
  have hgap := lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    (sourcePeriodicGapDisplacement hp hp1 ψ) n
  have hmid := lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    (sourceDirichletMidpointDisplacement hp hp1 ψ) n
  rw [sourceDirichletMidpointDisplacement_apply] at hmid
  apply (he ψ hψ.1 n).trans
  apply mul_le_mul_of_nonneg_left _ hC
  have hsum := (hb ψ hψ.2).1
  have hg := norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ n)
  linarith

/-- The literal spectral terminal preserves every native spectral weight locally over complex sources. -/
theorem exists_local_normalizedWeightedTerminal_bound
    (w : SpectralWeight) (φ : realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      (∀ ψ ∈ U, normalizedWeightedSource w ψ ∈ W) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ∀ sign : ℂ, sign = 1 ∨ sign = -1 →
        Memℓp (fun n => (w (2*n):ℂ)*sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign
          (normalizedWeightedSource w ψ)) p ∧
        ‖Coeff.ofFunctionOrZero p (fun n => (w (2*n):ℂ)*sourceGapWeightedEtaTerminalCoordinate
          hp hp1 n sign (normalizedWeightedSource w ψ))‖ ≤ M := by
  let φu : realTypeSourceSubmodule p :=
    ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Ve,hVe,hφe,hVeW,M₀,hM₀,he⟩ := D.exists_local_normalizedWeightedEta_bound w φ
  obtain ⟨Vr,hVr,hφr,_,A,hA,hr⟩ := D.exists_local_uniform_etaRemainder_bound φu
  let U := Ve ∩ normalizedWeightedSource w ⁻¹' Vr
  have hU : IsOpen U := hVe.inter (hVr.preimage (continuous_normalizedWeightedSource w))
  refine ⟨U,hU,⟨hφe,hφr⟩,(fun ψ hψ => hVeW ψ hψ.1),Real.exp A*M₀,by positivity,?_⟩
  intro ψ hψ sign hsign
  let e := normalizedWeightedEtaSequence hp hp1 s w sign ψ
  have hmem := (he ψ hψ.1 sign hsign).1
  have heval (n : ℤ) : e n = (w (2*n):ℂ)*sourceGapWeightedEtaCoordinate hp hp1 n s sign
      (normalizedWeightedSource w ψ) := Coeff.ofFunctionOrZero_apply_of_mem p _ hmem n
  have hsignnorm : ‖sign‖ = 1 := by rcases hsign with rfl | rfl <;> simp
  have hphase (n : ℤ) :
      ‖exp (-sign*I*sourceAngularEtaRemainder hp hp1 n s (normalizedWeightedSource w ψ))‖ ≤ Real.exp A := by
    apply (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    simpa only [norm_mul,norm_neg,hsignnorm,norm_I,one_mul] using hr _ hψ.2 n
  have hbound (n : ℤ) :
      ‖(w (2*n):ℂ)*sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign (normalizedWeightedSource w ψ)‖ ≤
        Real.exp A*(‖e n‖+‖(0 : Coeff p) n‖) := by
    rw [sourceGapWeightedEtaTerminalCoordinate_eq_inverse_phase hp hp1 n s,← mul_assoc,← heval]
    simpa only [norm_mul,lp.coeFn_zero,Pi.zero_apply,norm_zero,add_zero,mul_comm] using
      mul_le_mul_of_nonneg_left (hphase n) (norm_nonneg (e n))
  obtain ⟨hm,hn⟩ := Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound _ e 0
    (Real.exp A) (Real.exp_pos A).le hbound
  refine ⟨hm,hn.trans ?_⟩
  simpa only [norm_zero,add_zero,e,normalizedWeightedEtaSequence] using
    mul_le_mul_of_nonneg_left (he ψ hψ.1 sign hsign).2 (Real.exp_pos A).le

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
