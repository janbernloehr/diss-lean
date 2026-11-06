import NLS.ZakharovShabat.SourceZeroGapActionBound

/-! # The inverse-frequency mass moment in the actual real gap profiles -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem inverse_frequency_period_eq_realMoment
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hl : canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0)
    (n : ℤ) (hn : n ≠ 0)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    (∮ z in C(C.discs.center n,C.discs.inner n), sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z) =
      -2*(sourceRealGapInverseMoment hp hp1 φ n : ℂ) := by
  have hzero (z : ℂ) (hz : z ∈ closedBall (C.discs.center n) (C.discs.inner n)) : z ≠ 0 := by
    rintro rfl
    have ha := C.discs.avoids_other φ.val hφ n
      (closedBall_subset_closedBall (C.discs.inner_lt n).le hz) 0 hn.symm
    apply ha
    rw [←hl]
    exact left_mem_segment ℝ _ _
  have hw : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) (closedBall (C.discs.center n) (C.discs.inner n)) :=
    fun z hz => analyticAt_id.inv (hzero z hz)
  have hi := C.weighted_primitive_circle_eq_real_profile n φ hφ hgap (C.discs.inner n)
    le_rfl (C.discs.inner_lt n) (fun z : ℂ => z⁻¹) hw
  have he : (∫ θ in (0 : ℝ)..Real.pi,
      (sourceCanonicalRootGapPoint hp hp1 φ.val n (Real.cos θ))⁻¹*
        (sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ : ℂ))*
        (sourceRealGapCosineProfile hp hp1 φ.val n θ : ℂ)) =
      (sourceRealGapInverseMoment hp hp1 φ n : ℂ) := by
    rw [sourceRealGapInverseMoment,←intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro θ _hθ
    dsimp only
    rw [sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 φ.val φ.property n,
      sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 φ.val φ.property n]
    simp only [sourceRealGapMassDensity,canonicalPeriodicGap,sub_re,ofReal_inv,ofReal_mul,
      ofReal_ofNat,ofReal_sub,div_eq_mul_inv]
    ring
  rw [he] at hi
  rw [←hi]
  apply circleIntegral.integral_congr (C.discs.inner_pos n).le
  intro z _hz
  dsimp only
  ring

/-- The physical mass is twice the signed-index sum of the actual real
inverse-frequency gap integrals. The central term is absent by proof. -/
theorem mass_eq_sum_real_inverse_moments
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (hl : canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0)
    (hr : canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0) :
    (∑' k : ℤ, φ.val.fst k*φ.val.snd (-k)).re =
      2*∑ n ∈ hf.toFinset, (n : ℝ)*sourceRealGapInverseMoment hp hp1 φ n := by
  classical
  have hs (n : ℤ) : n ∈ hf.toFinset ↔ canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0 := Set.Finite.mem_toFinset hf
  have hgap0 : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0 := by
    rw [canonicalPeriodicGap,hl,hr,sub_self]
  have he := C.mass_eq_sum_inverse_frequency_periods φ hφ hf hl hr
  have hlocal (n : ℤ) (hn : n ∈ hf.toFinset) := C.inverse_frequency_period_eq_realMoment φ hφ hl n
    (by rintro rfl; exact (hs 0).mp hn hgap0) ((hs n).mp hn)
  have he' : (∑' k : ℤ, φ.val.fst k*φ.val.snd (-k)) =
      ((2*∑ n ∈ hf.toFinset, (n : ℝ)*sourceRealGapInverseMoment hp hp1 φ n : ℝ) : ℂ) := by
    rw [he]
    push_cast
    rw [Finset.mul_sum,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hlocal n hn]
    ring
  exact congrArg Complex.re he'

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
