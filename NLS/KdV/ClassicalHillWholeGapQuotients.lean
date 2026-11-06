import NLS.KdV.ClassicalHillSmallWholeGapSquares
import NLS.KdV.ClassicalHillWholeGapSquares
import NLS.KdV.FrequencyPrimitiveContinuation

/-! # Filled primitive/root quotients on complete actual high-gap discs

A single small derivative neighborhood for squaredCosh gives a nonzero
analytic quotient on each whole disc, with the actual continued sheet.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem sinh_add_hill_index (z : ℂ) (n : ℕ) :
    sinh (z+I*(n : ℂ)*Real.pi) = (-1 : ℂ)^n*sinh z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z+I*((n+1 : ℕ) : ℂ)*Real.pi =
        (z+I*(n : ℂ)*Real.pi)+(Real.pi : ℂ)*I := by push_cast; ring
    rw [he,sinh_add_pi_mul_I,ih,pow_succ]
    ring

/-- The actual root sheet is compatible with the indexed shifted primitive. -/
theorem classicalHill_shifted_primitive_sheet (n : ℕ+) (t : ℂ × Curve ℂ)
    (ht : t ∈ classicalHillContinuationDomain) :
    classicalHillContinuedRoot t = 2*((-1 : ℂ)^(n : ℕ))*
      sinh (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi) := by
  have hs : ((-1 : ℂ)^(n : ℕ))^2 = 1 := by rw [← pow_mul,Nat.mul_comm (n : ℕ) 2,pow_mul];norm_num
  rw [sinh_add_hill_index,← (classicalHillContinuedPrimitive_trace t ht).2]
  linear_combination -2*sinh (classicalHillContinuedPrimitive t)*hs

/-- A common complex source neighborhood and cutoff support both the
actual squared primitive and its filled root quotient on every whole disc.
The actual straight complex gap, including a collapsed pair, is enclosed. -/
theorem exists_classicalHill_whole_gap_quotients (q : Curve ℂ) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Curve ℂ),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K H : ℂ × Curve ℂ → ℂ,
        AnalyticOnNhd ℂ K (classicalHillGapSquareDisc n r ×ˢ V) ∧
        AnalyticOnNhd ℂ H (classicalHillGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V,
          H t ≠ 0 ∧ K t = (H t)^2*classicalHillRadicand t) ∧
        (∀ t ∈ (classicalHillGapSquareDisc n r ×ˢ V) ∩ classicalHillContinuationDomain,
          K t = (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2 ∧
          H t = (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)/classicalHillContinuedRoot t) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V, classicalHillRadicand t = 0 →
          K t = 0 ∧ H t = ((-1 : ℂ)^(n : ℕ))/2) ∧
        ∀ a ∈ V, ∃ l u : ℂ, ClassicalHillHighGapPair a n l u ∧
          segment ℝ l u ⊆ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by
  have hd := ((analyticOnNhd_squaredCosh 0 (mem_univ _)).deriv).continuousAt
  have hn : deriv squaredCosh 0 ≠ 0 := by rw [hasDerivAt_squaredCosh_zero.deriv];norm_num
  obtain ⟨B,hB,hbound⟩ := Metric.mem_nhds_iff.mp (hd.eventually_ne hn)
  obtain ⟨r,N,V,hr,hrpi,hN,hV,hq,hfamily⟩ := exists_classicalHill_whole_gap_small_squares q B hB
  refine ⟨r,N,V,hr,hrpi,hN,hV,hq,?_⟩
  intro n hnn
  obtain ⟨K,hK,hsmall,htrace,hzero,hmatch,hpair⟩ := hfamily n hnn
  let s : ℂ := (-1 : ℂ)^(n : ℕ)
  have hs : s^2 = 1 := by dsimp only [s];rw [← pow_mul,Nat.mul_comm (n : ℕ) 2,pow_mul];norm_num
  have hs0 : s ≠ 0 := by dsimp only [s];exact pow_ne_zero _ (by norm_num)
  let D : ℂ × Curve ℂ → ℂ := fun t => deriv squaredCosh (K t)
  have hD : AnalyticOnNhd ℂ D (classicalHillGapSquareDisc n r ×ˢ V) := by
    intro t ht
    exact ((analyticOnNhd_squaredCosh (K t) (mem_univ _)).deriv).comp (hK t ht)
  have hDn (t : ℂ × Curve ℂ) (ht : t ∈ classicalHillGapSquareDisc n r ×ˢ V) : D t ≠ 0 :=
    hbound (by simpa only [mem_ball,dist_zero_right] using hsmall t ht)
  let H : ℂ × Curve ℂ → ℂ := fun t => s/(4*D t)
  have hH : AnalyticOnNhd ℂ H (classicalHillGapSquareDisc n r ×ˢ V) :=
    analyticOnNhd_const.div (analyticOnNhd_const.mul hD) (fun t ht => mul_ne_zero (by norm_num) (hDn t ht))
  refine ⟨K,H,hK,hH,?_,?_,?_,hpair⟩
  · intro t ht
    refine ⟨div_ne_zero hs0 (mul_ne_zero (by norm_num) (hDn t ht)),?_⟩
    have hfac := squaredCosh_radicand_factorization (K t)
    rw [htrace t ht] at hfac
    have he : classicalHillRadicand t = 16*K t*(D t)^2 := by
      dsimp only [classicalHillRadicand,D]
      linear_combination hfac-(classicalHillDiscriminant t.2 t.1)^2*hs
    change K t = (s/(4*D t))^2*classicalHillRadicand t
    rw [he,div_pow,hs]
    field_simp [hDn t ht]
    ring
  · intro t ht
    refine ⟨hmatch t ht,?_⟩
    exact primitive_root_ratio_eq s _ (K t) _ hs (hmatch t ht).symm
      (classicalHill_shifted_primitive_sheet n t ht.2)
      (classicalHillContinuedRoot_ne_zero t ht.2) (hDn t ht.1)
  · intro t ht hz
    have hK0 := (hzero t ht).mpr hz
    refine ⟨hK0,?_⟩
    change s/(4*deriv squaredCosh (K t)) = s/2
    rw [hK0,hasDerivAt_squaredCosh_zero.deriv]
    ring

end NLS.KdV
