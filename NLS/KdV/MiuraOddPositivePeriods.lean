import NLS.KdV.MiuraHillPsiNumerators
import NLS.KdV.HillMiuraPositiveGaps
import NLS.ZakharovShabat.SourceSymmetricCentralCircle
import NLS.ComplexAnalysis.EvenCircleIntegral

/-! For an odd entire frequency numerator over the ACTUAL odd Miura
root, positive gap periods determine all signed periods. An actual
zero-centered central circle supplies its zero period automatically. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_all_signed_zero_periods_of_positive
    (A : MiuraHillPsiFamily) (u : PeriodOneRealL2) (F : ℂ → ℂ) (hodd : ∀ z : ℂ, F (-z) = -F z)
    (hpositive : ∀ m : ℕ+, ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) ((m:ℕ):ℤ),
      (∮ z in C((D.center:ℂ),D.radius),
        F z/sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) z) = 0) :
    ∀ m : ℤ, ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) m,
      (∮ z in C((D.center:ℂ),D.radius),
        F z/sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) z) = 0 := by
  let f : ℂ → ℂ := fun z => F z/sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) z
  have heven (z : ℂ) : f (-z) = f z := by
    dsimp only [f]
    rw [hodd,sourceCanonicalRoot_hillMiuraDiagonal_neg]
    exact neg_div_neg_eq _ _
  intro m
  rcases lt_trichotomy m 0 with hm | hm | hm
  · let k : ℕ+ := ⟨(-m).toNat,by omega⟩
    have hk : -((k:ℕ):ℤ) = m := by
      change -(((-m).toNat:ℕ):ℤ) = m
      rw [Int.toNat_of_nonneg (by omega)]
      exact neg_neg m
    obtain ⟨D,hD⟩ := hpositive k
    let E := (sourcePeriodicReflection_hillMiuraDiagonal u.val).periodCircleNeg D
    have hE : (∮ z in C((E.center:ℂ),E.radius), f z) = 0 := by
      change (∮ z in C(((-D.center:ℝ):ℂ),D.radius), f z) = 0
      rw [Complex.ofReal_neg,circleIntegral_even_neg_center f heven,hD,neg_zero]
    have hx : ∃ E : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
        (hillMiuraDiagonal u.val) (-((k:ℕ):ℤ)), (∮ z in C((E.center:ℂ),E.radius), f z) = 0 := ⟨E,hE⟩
    rw [hk] at hx
    simpa only [f] using hx
  · subst m
    obtain ⟨D⟩ := A.verified.nonempty_periodCircle (hillMiuraDiagonal u.val) (A.real_mem_source u) 0
    have hzero : (0:ℂ) ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) 0 := by
      simpa only [Complex.ofReal_zero] using sourcePeriodicSegment_mem_of_realIcc
        (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property 0 0
        (hillMiura_gap_zero_contains_zero u)
    let E := (sourcePeriodicReflection_hillMiuraDiagonal u.val).zeroCenteredPeriodCircle D hzero
    refine ⟨E,?_⟩
    change (∮ z in C(0,D.radius), f z) = 0
    exact circleIntegral_even_center_zero f heven D.radius
  · let k : ℕ+ := ⟨m.toNat,by omega⟩
    have hk : ((k:ℕ):ℤ) = m := by
      change ((m.toNat:ℕ):ℤ) = m
      exact Int.toNat_of_nonneg hm.le
    have hx := hpositive k
    rw [hk] at hx
    exact hx

end NLS.KdV
