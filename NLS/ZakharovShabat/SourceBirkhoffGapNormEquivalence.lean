import NLS.ZakharovShabat.SourceBirkhoffWeightedMembership
import NLS.ZakharovShabat.SourceSection14

/-! # Two-sided comparison of real Birkhoff coordinates and spectral gaps

A common positive lower bound on the normalized actions controls every gap
by the two real rectangular coordinates, uniformly near each real source.
Together with the forward bound this characterizes weighted membership
of the actual gap sequence by that of the original coordinate pair.
The weight need only be positive; source regularity is not inferred.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- One positive constant controls all squared gaps on a common real source neighborhood. -/
theorem exists_local_uniform_gap_sq_le_real_map_radius
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ ∃ c : ℝ, 0 < c ∧
      ∀ ψ : realTypeSourceSubmodule p, ψ.val ∈ U → ∀ n : ℤ,
        c * ‖sourcePeriodicGapDisplacement hp hp1 ψ.val n‖^2 ≤
          ((sourceRealBirkhoffMap hp hp1 s ψ).1 n)^2 +
            ((sourceRealBirkhoffMap hp hp1 s ψ).2 n)^2 := by
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨U,hU,hφU,c,hc,hpos⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_uniform_re_pos
      (q := p) hp hp1 hp1 hp hhalf φ.val φ.property
  obtain ⟨V,hV,hφV,_,hfactor⟩ :=
    exists_local_sourceNormalizedAction_allIndices_analytic_factor hp hp1 φ.val φ.property
  refine ⟨U ∩ V,hU.inter hV,⟨hφU,hφV⟩,c/2,half_pos hc,?_⟩
  intro ψ hψ n
  obtain ⟨hIpos,hIim,_⟩ := sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 ψ.val ψ.property n
  have he : sourceRealAction hp hp1 ψ.val ψ.property n =
      ((sourceRealAction hp hp1 ψ.val ψ.property n).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hIim
  have hnI : ‖sourceComplexAction hp hp1 n ψ.val‖ =
      (sourceRealAction hp hp1 ψ.val ψ.property n).re := by
    rw [sourceComplexAction_eq_sourceRealAction hp hp1 n ψ.val ψ.property, he]
    exact Complex.norm_of_nonneg hIpos
  have hF := congrArg norm (hfactor ψ.val hψ.2 n)
  rw [norm_mul, norm_pow, hnI] at hF
  have hnorm := (hpos ψ.val hψ.1 n).trans
    (Complex.re_le_norm (4*sourceNormalizedActionComplexExtension hp hp1 n ψ.val))
  rw [norm_mul, show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num] at hnorm
  have hbound := mul_le_mul_of_nonneg_left hnorm (sq_nonneg ‖sourcePeriodicGapDisplacement hp hp1 ψ.val n‖)
  rw [D.real_map_action_radius]
  nlinarith [hF]

/-- The gap lengths are bounded by the original rectangular coordinates, locally uniformly. -/
theorem exists_local_uniform_gap_le_real_map
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ ∃ A : ℝ, 0 < A ∧
      ∀ ψ : realTypeSourceSubmodule p, ψ.val ∈ U → ∀ n : ℤ,
        ‖sourcePeriodicGapDisplacement hp hp1 ψ.val n‖ ≤
          A * (|(sourceRealBirkhoffMap hp hp1 s ψ).1 n| +
            |(sourceRealBirkhoffMap hp hp1 s ψ).2 n|) := by
  obtain ⟨U,hU,hφU,c,hc,hbound⟩ := D.exists_local_uniform_gap_sq_le_real_map_radius φ
  have hsqrt := Real.sqrt_pos.mpr hc
  refine ⟨U,hU,hφU,(Real.sqrt c)⁻¹,inv_pos.mpr hsqrt,?_⟩
  intro ψ hψ n
  let x := (sourceRealBirkhoffMap hp hp1 s ψ).1 n
  let y := (sourceRealBirkhoffMap hp hp1 s ψ).2 n
  let g := ‖sourcePeriodicGapDisplacement hp hp1 ψ.val n‖
  have hsq : (Real.sqrt c * g)^2 ≤ (|x|+|y|)^2 := by
    rw [mul_pow,Real.sq_sqrt hc.le]
    have h := hbound ψ hψ n
    change c*g^2 ≤ x^2+y^2 at h
    nlinarith [sq_abs x,sq_abs y,mul_nonneg (abs_nonneg x) (abs_nonneg y)]
  have h := (sq_le_sq₀ (mul_nonneg hsqrt.le (norm_nonneg _))
    (add_nonneg (abs_nonneg x) (abs_nonneg y))).mp hsq
  calc
    g = (Real.sqrt c)⁻¹ * (Real.sqrt c * g) := by
      rw [← mul_assoc,inv_mul_cancel₀ hsqrt.ne',one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hsqrt.le)

/-- The actual gap sequence and original real coordinate pair have exactly the same positive weights. -/
theorem weighted_gap_mem_iff_real_map_mem
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : Weight) (φ : realTypeSourceSubmodule p) :
    Memℓp (fun n : ℤ => (w n : ℂ) * sourcePeriodicGapDisplacement hp hp1 φ.val n) p ↔
      Memℓp (fun n : ℤ => w n * (sourceRealBirkhoffMap hp hp1 s φ).1 n) p ∧
        Memℓp (fun n : ℤ => w n * (sourceRealBirkhoffMap hp hp1 s φ).2 n) p := by
  constructor
  · intro hg
    obtain ⟨A,_,hb⟩ := D.real_map_gap_bound φ
    have hmajor := hg.norm.const_mul A
    constructor
    · apply hmajor.mono
      intro n
      simpa only [norm_mul, Real.norm_eq_abs, Complex.norm_real,
        abs_of_pos (w.positive _), mul_left_comm (w n) A] using
        (mul_le_mul_of_nonneg_left (hb n).1 (w.positive n).le)
    · apply hmajor.mono
      intro n
      simpa only [norm_mul, Real.norm_eq_abs, Complex.norm_real,
        abs_of_pos (w.positive _), mul_left_comm (w n) A] using
        (mul_le_mul_of_nonneg_left (hb n).2 (w.positive n).le)
  · rintro ⟨hx,hy⟩
    obtain ⟨U,_,hφU,A,_,hb⟩ := D.exists_local_uniform_gap_le_real_map φ
    apply ((hx.norm.add hy.norm).const_mul A).mono
    intro n
    simpa only [norm_mul, Real.norm_eq_abs, Complex.norm_real,
      abs_of_pos (w.positive _), Pi.add_apply, ← mul_add, mul_left_comm (w n) A] using
      mul_le_mul_of_nonneg_left (hb φ hφU n) (w.positive n).le

end SourceBirkhoffMapComplexData

/-- The constructed original map has the gap/coordinate weighted-membership equivalence at every real source. -/
theorem sourceSection14_weighted_gap_characterization (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ _D : SourceSection14Data hp hp1 W₀ W V s,
        ∀ w : Weight, ∀ φ : realTypeSourceSubmodule p,
          Memℓp (fun n : ℤ => (w n : ℂ) * sourcePeriodicGapDisplacement hp hp1 φ.val n) p ↔
            Memℓp (fun n : ℤ => w n * (sourceRealBirkhoffMap hp hp1 s φ).1 n) p ∧
              Memℓp (fun n : ℤ => w n * (sourceRealBirkhoffMap hp hp1 s φ).2 n) p := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 hp hp1
  exact ⟨W₀,W,V,s,D,fun w φ => D.complex.weighted_gap_mem_iff_real_map_mem w φ⟩

end NLS.ZakharovShabat
