import NLS.ZakharovShabat.SourceCriticalHalfExponentOffsets
import NLS.ZakharovShabat.SourceSingleRootQuotientAsymptoticDiscSup

/-! # Locally uniform sequence majorants for the deleted critical factor

The actual critical-midpoint offset supplies the numerator displacement
in Lemma 10.8. Half-exponent control and contractive sequence inclusions
remove the auxiliary displacement hypotheses from that product estimate.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Critical deleted-factor errors on distant free discs have locally
bounded `ell^q + ell^(p/2)` majorants whenever `q > 1` and `p/2 ≤ q`. -/
theorem exists_local_sourceCriticalFactorDiscMajorants
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (hpq : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ K : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ ψ ∈ V, ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
        ‖Bq‖ ≤ M ∧ ‖Bg‖ ≤ M ∧ ∀ n : ℤ, K ≤ n.natAbs →
          ∀ z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4),
            ‖sourceSingleRootQuotientJointProduct hp hp1 n
              (z,(canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ),ψ))-1‖ ≤
                ‖Bq n‖+‖Bg n‖ := by
  obtain ⟨Va,hVa,hφa,L,hL,ha⟩ := exists_local_uniform_sourceCriticalHalfOffsets hp hp1 φ hφ
  obtain ⟨N,ε,_,_,Vd,hVd,_,hφd,C,R,H,hC,hR,hH,K,hNK,hd⟩ :=
    exists_local_sourceSingleRootQuotientDiscMajorants hp hp1 hq1 hq φ hφ
  let F : ℝ → ℝ := fun x =>
    (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+‖Fourier.hilbertSquareCoeffs‖)+
      C*R*‖Fourier.hilbertSquareCoeffs‖)*x+
      Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*x)*
        ((C/2)*Fourier.absoluteSampledRowConstant hq*x)^2
  let G : ℝ → ℝ := fun x =>
    (Real.exp (C*x*‖Coeff.puncturedLattice q.conjExponent
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖)*C^2)*
      (H^2*‖squaredReciprocalKernel (min 1 (p.toReal/2))
        (lt_min (by norm_num : (1/2:ℝ)<1) (by
          have hpr : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
          linarith))‖)
  obtain ⟨MF,hMF⟩ := (isCompact_Icc (a := (0:ℝ)) (b := L)).exists_bound_of_continuousOn
    (f := F) (by dsimp [F]; fun_prop)
  obtain ⟨MG,hMG⟩ := (isCompact_Icc (a := (0:ℝ)) (b := L)).exists_bound_of_continuousOn
    (f := G) (by dsimp [G]; fun_prop)
  refine ⟨Va ∩ Vd,hVa.inter hVd,⟨hφa,hφd⟩,K,max (max MF MG) 0,le_max_right _ _,?_⟩
  intro ψ hψ
  let α : Coeff q := ⟨fun n => sourceCriticalHalfGapOffset hp hp1 ψ n,
    (lp.memℓp (sourceCriticalHalfGapOffset hp hp1 ψ)).of_exponent_ge hpq⟩
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hα : ‖α‖ ≤ L := (Coeff.norm_quasiExponentInclusion_le
    (ENNReal.ofReal_pos.mpr (by positivity)) (zero_lt_one.trans hq1) hq hpq _).trans (ha ψ hψ.1).1
  have he : ∀ n : ℤ,
      displacedRoots (canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) n-
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = α n := by
    intro n
    simp only [displacedRoots,canonicalCriticalDisplacement_apply,add_sub_cancel]
    exact ((ha ψ hψ.1).2.2 n).1
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ := hd ψ hψ.2 _ α he
  refine ⟨Bq,Bg,?_,?_,?_⟩
  · exact hBq.trans ((le_abs_self (F ‖α‖)).trans ((hMF _ ⟨norm_nonneg _,hα⟩).trans
      ((le_max_left _ _).trans (le_max_left _ _))))
  · exact hBg.trans ((le_abs_self (G ‖α‖)).trans ((hMG _ ⟨norm_nonneg _,hα⟩).trans
      ((le_max_right _ _).trans (le_max_left _ _))))
  · intro n hn z hz
    apply hpoint n hn z
    simpa only [sourceIsolatingDisc,if_neg (show ¬n.natAbs ≤ N by omega),refinedResonantDisk] using hz

/-- When the half exponent is at most one, the critical deleted factor
has an `ell^q + ell^(p/2)` majorant for every finite `q > 1`. -/
theorem exists_local_sourceCriticalFactorDiscMajorants_one
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (hpq : ENNReal.ofReal (p.toReal/2) ≤ 1)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ K : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ ψ ∈ V, ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
        ‖Bq‖ ≤ M ∧ ‖Bg‖ ≤ M ∧ ∀ n : ℤ, K ≤ n.natAbs →
          ∀ z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4),
            ‖sourceSingleRootQuotientJointProduct hp hp1 n
              (z,(canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ),ψ))-1‖ ≤
                ‖Bq n‖+‖Bg n‖ := by
  obtain ⟨Va,hVa,hφa,L,hL,ha⟩ := exists_local_uniform_sourceCriticalHalfOffsets hp hp1 φ hφ
  obtain ⟨N,ε,_,_,Vd,hVd,_,hφd,C,R,H,hC,hR,hH,K,hNK,hd⟩ :=
    exists_local_sourceSingleRootQuotientDiscMajorants_one hq1 hq hp hp1 φ hφ
  let F : ℝ → ℝ := fun x =>
    (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+‖Fourier.hilbertSquareCoeffs‖)+
      C*R*‖Fourier.hilbertSquareCoeffs‖)*x+
      Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*x)*
        ((C/2)*Fourier.absoluteSampledRowConstant hq*x)^2
  let G : ℝ → ℝ := fun x =>
    (Real.exp (C*x*‖Coeff.puncturedLattice (1:ℝ≥0∞).conjExponent
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt (1:ℝ≥0∞) (1:ℝ≥0∞).conjExponent).mp (by norm_num : (1:ℝ≥0∞)<⊤))‖)*C^2)*
      (H^2*‖squaredReciprocalKernel (min 1 (p.toReal/2))
        (lt_min (by norm_num : (1/2:ℝ)<1) (by
          have hpr : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
          linarith))‖)
  obtain ⟨MF,hMF⟩ := (isCompact_Icc (a := (0:ℝ)) (b := L)).exists_bound_of_continuousOn
    (f := F) (by dsimp [F]; fun_prop)
  obtain ⟨MG,hMG⟩ := (isCompact_Icc (a := (0:ℝ)) (b := L)).exists_bound_of_continuousOn
    (f := G) (by dsimp [G]; fun_prop)
  refine ⟨Va ∩ Vd,hVa.inter hVd,⟨hφa,hφd⟩,K,max (max MF MG) 0,le_max_right _ _,?_⟩
  intro ψ hψ
  let α : Coeff 1 := ⟨fun n => sourceCriticalHalfGapOffset hp hp1 ψ n,
    (lp.memℓp (sourceCriticalHalfGapOffset hp hp1 ψ)).of_exponent_ge hpq⟩
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hα : ‖α‖ ≤ L := (Coeff.norm_quasiExponentInclusion_le
    (ENNReal.ofReal_pos.mpr (by positivity)) (by norm_num) (by norm_num) hpq _).trans (ha ψ hψ.1).1
  have hαq : ‖Coeff.exponentInclusion hq1.le α‖ ≤ L :=
    (Coeff.norm_exponentInclusion_le hq1.le α).trans hα
  have he : ∀ n : ℤ,
      displacedRoots (canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) n-
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = α n := by
    intro n
    simp only [displacedRoots,canonicalCriticalDisplacement_apply,add_sub_cancel]
    exact ((ha ψ hψ.1).2.2 n).1
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ := hd ψ hψ.2 _ α he
  refine ⟨Bq,Bg,?_,?_,?_⟩
  · exact hBq.trans ((le_abs_self (F ‖Coeff.exponentInclusion hq1.le α‖)).trans ((hMF _ ⟨norm_nonneg _,hαq⟩).trans
      ((le_max_left _ _).trans (le_max_left _ _))))
  · exact hBg.trans ((le_abs_self (G ‖α‖)).trans ((hMG _ ⟨norm_nonneg _,hα⟩).trans
      ((le_max_right _ _).trans (le_max_left _ _))))
  · intro n hn z hz
    apply hpoint n hn z
    simpa only [sourceIsolatingDisc,if_neg (show ¬n.natAbs ≤ N by omega),refinedResonantDisk] using hz

/-- The deleted critical product has precisely the mixed sequence
majorant required by Lemma 19.4, for every finite exponent above one. -/
theorem exists_local_sourceCriticalFactor_mixed_majorants
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ K : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ ψ ∈ V, ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
        ‖Bq‖ ≤ M ∧ ‖Bg‖ ≤ M ∧ ∀ n : ℤ, K ≤ n.natAbs →
          ∀ z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4),
            ‖sourceSingleRootQuotientJointProduct hp hp1 n
              (z,(canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ),ψ))-1‖ ≤
                ‖Bq n‖+‖Bg n‖ := by
  let ρ := ENNReal.ofReal (p.toReal/2)
  by_cases hρ : ρ ≤ 1
  · exact exists_local_sourceCriticalFactorDiscMajorants_one hp hp1 hq hq1 hρ φ hφ
  have hρ1 : 1 < ρ := lt_of_not_ge hρ
  let : Fact (1 ≤ ρ) := ⟨hρ1.le⟩
  obtain ⟨V,hV,hφV,K,M,hM,hb⟩ := exists_local_sourceCriticalFactorDiscMajorants
    hp hp1 (q := ρ) ENNReal.ofReal_ne_top hρ1 le_rfl φ hφ
  refine ⟨V,hV,hφV,K,2*M,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨Ba,Bg,hBa,hBg,hpoint⟩ := hb ψ hψ
  let B : Coeff ρ := Coeff.magnitude Ba+Coeff.magnitude Bg
  have hnB : ‖B‖ ≤ 2*M := by
    apply (norm_add_le _ _).trans
    rw [Coeff.norm_magnitude_quasi (zero_lt_one.trans hρ1).ne',
      Coeff.norm_magnitude_quasi (zero_lt_one.trans hρ1).ne']
    linarith
  refine ⟨0,B,by simpa only [norm_zero] using (mul_nonneg (by norm_num : (0:ℝ)≤2) hM),hnB,?_⟩
  intro n hn z hz
  have he : ‖B n‖ = ‖Ba n‖+‖Bg n‖ := by
    simp only [B,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  simpa only [lp.coeFn_zero,Pi.zero_apply,norm_zero,zero_add,he] using hpoint n hn z hz

end NLS.ZakharovShabat
