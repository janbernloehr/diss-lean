import NLS.ZakharovShabat.RealGapCanonicalRootValue
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic

/-!
# Constant sign of the canonical-root boundary value on a real gap

On a real open gap, the upper canonical-root boundary value and the
positive real square root have the same square. Both are continuous
and nonzero, so connectedness fixes their relative sign throughout
the gap.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed half-discriminant is continuous on the real axis. -/
theorem continuous_realGapHalfDiscriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0)
    (n : ℤ) :
    Continuous (realGapHalfDiscriminant hp φ n) := by
  have hc : Continuous (fun x : ℝ => (canonicalDiscriminant hp φ x).re) :=
    continuous_re.comp ((continuousOn_univ.mp
      (analyticOnNhd_canonicalDiscriminant hp hp1 φ heven).continuousOn).comp
        continuous_ofReal)
  by_cases hn : n % 2 = 0
  · have he : realGapHalfDiscriminant hp φ n =
        fun x : ℝ => (canonicalDiscriminant hp φ x).re/2 := by
      funext x
      simp [realGapHalfDiscriminant,hn]
    rw [he]
    exact hc.div_const 2
  · have he : realGapHalfDiscriminant hp φ n =
        fun x : ℝ => -(canonicalDiscriminant hp φ x).re/2 := by
      funext x
      simp [realGapHalfDiscriminant,hn]
    rw [he]
    exact hc.neg.div_const 2

/-- The signed half-discriminant radicand is positive at every
interior affine parameter of an open real canonical gap. -/
theorem realGapHalfDiscriminant_radicand_pos_at_affinePoint
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    0 < (realGapHalfDiscriminant hp (periodOnePotential ψ) n
      (realGapAffinePoint hp hp1 ψ n t))^2-1 := by
  let x := realGapAffinePoint hp hp1 ψ n t
  have hx := realGapAffinePoint_mem_Ioo hp hp1 ψ n hopen ht
  have hGpos := canonicalDeletedPeriodicProduct_re_pos_on_realGap_interior
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n x hx
  rw [realGapHalfDiscriminant_sq_sub_one_eq_deletedPair_re
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n x]
  exact mul_pos (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)) hGpos

/-- The upper canonical-root boundary value varies continuously
with the affine parameter on the interior of a real-type gap. -/
theorem continuousOn_sourceCanonicalRootGapUpperValue_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    ContinuousOn (sourceCanonicalRootGapUpperValue hp hp1 ψ n)
      (Ioo (-1:ℝ) 1) := by
  obtain ⟨W,_,_,hrealW,hdata⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  have hψW : ψ ∈ W := hrealW hreal
  have hPanalytic := sourceStandardRootOmittedProduct_analyticOnNhd_spectral
    hp hp1 n W (hdata n).2.1 ψ hψW
  obtain ⟨W',_,_,hrealW',hpoint⟩ :=
    exists_global_source_gapPoint_mem_omittedDomain hp hp1
  have hpath : Continuous (sourceCanonicalRootGapPoint hp hp1 ψ n) := by
    unfold sourceCanonicalRootGapPoint
    fun_prop
  have hPpath : ContinuousOn
      (fun t : ℝ => sourceStandardRootOmittedProduct hp hp1 n ψ
        (sourceCanonicalRootGapPoint hp hp1 ψ n t))
      (Ioo (-1:ℝ) 1) :=
    hPanalytic.continuousOn.comp hpath.continuousOn
      (fun t ht => hpoint ψ (hrealW' hreal) n t ht.1.le ht.2.le)
  have hroot : ContinuousOn
      (fun t : ℝ => 2*I * (-sourceStandardRootHalfGap hp hp1 ψ n * I *
        (Real.sqrt (1-t^2):ℂ))) (Ioo (-1:ℝ) 1) := by
    fun_prop
  change ContinuousOn (fun t : ℝ =>
    (2*I * (-sourceStandardRootHalfGap hp hp1 ψ n * I *
      (Real.sqrt (1-t^2):ℂ))) *
      sourceStandardRootOmittedProduct hp hp1 n ψ
        (sourceCanonicalRootGapPoint hp hp1 ψ n t)) (Ioo (-1:ℝ) 1)
  exact hroot.mul hPpath

/-- The upper canonical-root value has one fixed sign relative to the
positive arcosh square root on the entire open gap. -/
theorem sourceCanonicalRootGapUpperValue_eq_or_eq_neg_two_sqrt
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (∀ t ∈ Ioo (-1:ℝ) 1,
      sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
        ((2*Real.sqrt ((realGapHalfDiscriminant hp
          (periodOnePotential ψ) n (realGapAffinePoint hp hp1 ψ n t))^2-1):ℝ):ℂ)) ∨
    (∀ t ∈ Ioo (-1:ℝ) 1,
      sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
        -((2*Real.sqrt ((realGapHalfDiscriminant hp
          (periodOnePotential ψ) n (realGapAffinePoint hp hp1 ψ n t))^2-1):ℝ):ℂ)) := by
  let g := realGapHalfDiscriminant hp (periodOnePotential ψ) n
  let x := realGapAffinePoint hp hp1 ψ n
  let F := sourceCanonicalRootGapUpperValue hp hp1 ψ n
  let R (t : ℝ) : ℂ := ((2*Real.sqrt ((g (x t))^2-1):ℝ):ℂ)
  have hF : ContinuousOn F (Ioo (-1:ℝ) 1) :=
    continuousOn_sourceCanonicalRootGapUpperValue_realType hp hp1 ψ hreal n
  have hx : Continuous x := by
    unfold x realGapAffinePoint
    fun_prop
  have hg : Continuous g :=
    continuous_realGapHalfDiscriminant hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
  have hrad : Continuous (fun t : ℝ => (g (x t))^2-1) :=
    ((hg.comp hx).pow 2).sub continuous_const
  have hR : ContinuousOn R (Ioo (-1:ℝ) 1) := by
    have h : Continuous R :=
      continuous_ofReal.comp (continuous_const.mul
        (Real.continuous_sqrt.comp hrad))
    exact h.continuousOn
  have hRne : ∀ {t : ℝ}, t ∈ Ioo (-1:ℝ) 1 → R t ≠ 0 := by
    intro t ht
    have hp0 := realGapHalfDiscriminant_radicand_pos_at_affinePoint
      hp hp1 ψ hreal n hopen ht
    have hne : (2*Real.sqrt ((g (x t))^2-1):ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr hp0))
    change ((2*Real.sqrt ((g (x t))^2-1):ℝ):ℂ) ≠ 0
    exact_mod_cast hne
  have hsq : EqOn (F^2) (R^2) (Ioo (-1:ℝ) 1) := by
    intro t ht
    change F t ^ 2 = R t ^ 2
    have hbase := sourceCanonicalRootGapUpperValue_sq_eq_four_realGapHalfDiscriminant
      hp hp1 ψ hreal n t ht.1.le ht.2.le
    have hp0 := realGapHalfDiscriminant_radicand_pos_at_affinePoint
      hp hp1 ψ hreal n hopen ht
    have hrealSq : (2*Real.sqrt ((g (x t))^2-1))^2 =
        4*((g (x t))^2-1) := by
      rw [mul_pow,Real.sq_sqrt hp0.le]
      ring
    change F t ^ 2 = ((4*((g (x t))^2-1):ℝ):ℂ) at hbase
    rw [hbase]
    change ((4*((g (x t))^2-1):ℝ):ℂ) =
      (((2*Real.sqrt ((g (x t))^2-1):ℝ):ℂ))^2
    exact_mod_cast hrealSq.symm
  have hsign := isPreconnected_Ioo.eq_or_eq_neg_of_sq_eq hF hR hsq hRne
  simpa only [EqOn,Pi.pow_apply,Pi.neg_apply,F,R,g,x] using hsign

end NLS.ZakharovShabat
