import NLS.ZakharovShabat.SourceWeightedEtaComplexAnalytic
import NLS.ZakharovShabat.SourceEtaRemainderLocalGapBound

/-! Weighted bounds for the ACTUAL Dirichlet-to-midpoint displacement,
obtained directly from the two eta signs and their inverse remainder phases. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- One complex neighborhood bounds every actual eta remainder. -/
theorem exists_local_uniform_ownEtaRemainder_bound (φ : realTypeSourceSubmodule 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ W ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        ‖sourceAngularEtaRemainder (by simp) (by norm_num) n s ψ‖ ≤ A := by
  obtain ⟨Ve,hVe,hφe,hVeW,C,hC,he⟩ := D.exists_local_uniform_etaRemainder_gap_bound φ
  obtain ⟨Vb,hVb,hφb,_,G,A,hG,_,hb⟩ := D.angular.exists_local_uniform_betaCorrection_bound
    φ.val (D.source_subset (D.real_subset φ.property))
  refine ⟨Ve ∩ Vb,hVe.inter hVb,⟨hφe,hφb⟩,
    (fun _ hψ => hVeW hψ.1),C*G,mul_nonneg hC hG,?_⟩
  intro ψ hψ n
  have hgap := lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ (2:ℝ≥0∞))).ne'
    (sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ) n
  have hmid := lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ (2:ℝ≥0∞))).ne'
    (sourceDirichletMidpointDisplacement (by simp) (by norm_num) ψ) n
  rw [sourceDirichletMidpointDisplacement_apply] at hmid
  apply (he ψ hψ.1 n).trans
  apply mul_le_mul_of_nonneg_left _ hC
  have hsum := (hb ψ hψ.2).1
  have hg := norm_nonneg (sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ n)
  linarith

/-- The weighted ACTUAL midpoint displacement has a bounded Hilbert realization
on one complex neighborhood of each normalized real weighted source. -/
theorem exists_local_normalizedWeightedMidpoint_bound
    (w : SpectralWeight) (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val∈U ∧
      (∀ ψ∈U, normalizedWeightedSource w ψ∈W) ∧
      ∃ M : ℝ, 0≤M ∧ ∀ ψ∈U, ∃ A : Coeff 2,
        (∀ n, A n=(w (2*n):ℂ)*sourceDirichletMidpointDisplacement
          (by simp) (by norm_num) (normalizedWeightedSource w ψ) n) ∧ ‖A‖≤M := by
  let φu : realTypeSourceSubmodule 2 :=
    ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Ve,hVe,hφe,hVeW,M₀,hM₀,he⟩ := D.exists_local_normalizedWeightedEta_bound w φ
  obtain ⟨Vr,hVr,hφr,_hVrW,A,hA,hr⟩ := D.exists_local_uniform_ownEtaRemainder_bound φu
  let U := Ve∩normalizedWeightedSource w ⁻¹' Vr
  refine ⟨U,hVe.inter (hVr.preimage (continuous_normalizedWeightedSource w)),
    ⟨hφe,hφr⟩,(fun ψ hψ => hVeW ψ hψ.1),Real.exp A*(M₀+M₀),by positivity,?_⟩
  intro ψ hψ
  let χ := normalizedWeightedSource w ψ
  let e := normalizedWeightedEtaSequence (by simp) (by norm_num) s w 1 ψ
  let f := normalizedWeightedEtaSequence (by simp) (by norm_num) s w (-1) ψ
  have hec (n : ℤ) : e n=(w (2*n):ℂ)*sourceGapWeightedEtaCoordinate
      (by simp) (by norm_num) n s 1 χ :=
    Coeff.ofFunctionOrZero_apply_of_mem 2 _ (he ψ hψ.1 1 (Or.inl rfl)).1 n
  have hfc (n : ℤ) : f n=(w (2*n):ℂ)*sourceGapWeightedEtaCoordinate
      (by simp) (by norm_num) n s (-1) χ :=
    Coeff.ofFunctionOrZero_apply_of_mem 2 _ (he ψ hψ.1 (-1) (Or.inr rfl)).1 n
  let R := fun n => sourceAngularEtaRemainder (by simp) (by norm_num) n s χ
  have hphase (n : ℤ) : ‖exp (-I*R n)‖≤Real.exp A ∧ ‖exp (I*R n)‖≤Real.exp A := by
    constructor <;> apply (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    · simpa only [norm_mul,norm_neg,norm_I,one_mul,R] using hr _ hψ.2 n
    · simpa only [norm_mul,norm_I,one_mul,R] using hr _ hψ.2 n
  have hcancel (sign : ℂ) (n : ℤ) :
      ((w (2*n):ℂ)*sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s sign χ)*
        exp (-sign*I*R n)=
      (w (2*n):ℂ)*(-2*(canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet χ n-
        canonicalPeriodicMidpoint (by simp) (by norm_num) (periodOnePotential χ) (periodOnePotential_mem χ) n+
          sign*I*sourceDirichletEtaSineNumerator (by simp) (by norm_num) n χ)) := by
    rw [sourceGapWeightedEtaCoordinate,mul_assoc,mul_assoc,←exp_add]
    have hz : sign*I*sourceAngularEtaRemainder (by simp) (by norm_num) n s χ+-sign*I*R n=0 := by
      dsimp only [R]
      ring
    rw [hz,exp_zero,mul_one]
  let g := fun n : ℤ => (w (2*n):ℂ)*sourceDirichletMidpointDisplacement (by simp) (by norm_num) χ n
  have hg (n : ℤ) : g n=(-(1/4):ℂ)*(e n*exp (-I*R n)+f n*exp (I*R n)) := by
    have hp := hcancel 1 n
    have hm := hcancel (-1) n
    simp only [one_mul,neg_one_mul,neg_neg] at hp hm
    rw [hec,hfc,hp,hm]
    dsimp only [g]
    rw [sourceDirichletMidpointDisplacement_apply]
    ring
  have hb (n : ℤ) : ‖g n‖≤Real.exp A*(‖e n‖+‖f n‖) := by
    rw [hg,norm_mul]
    have hq : ‖(-(1/4):ℂ)‖≤1 := by norm_num [norm_div]
    apply (mul_le_mul_of_nonneg_right hq (norm_nonneg _)).trans
    rw [one_mul]
    exact (norm_add_le _ _).trans (by
      rw [norm_mul,norm_mul]
      nlinarith [(hphase n).1,(hphase n).2,norm_nonneg (e n),norm_nonneg (f n)])
  obtain ⟨hm,hn⟩ := Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound
    g e f (Real.exp A) (Real.exp_pos A).le hb
  refine ⟨Coeff.ofFunctionOrZero 2 g,fun n => Coeff.ofFunctionOrZero_apply_of_mem 2 g hm n,?_⟩
  exact hn.trans (mul_le_mul_of_nonneg_left (add_le_add
    (he ψ hψ.1 1 (Or.inl rfl)).2 (he ψ hψ.1 (-1) (Or.inr rfl)).2) (Real.exp_pos A).le)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
