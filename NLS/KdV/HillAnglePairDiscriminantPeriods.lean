import NLS.KdV.HillAnglePairDiscriminantVariation
import NLS.KdV.HillFunctionalActionPrescribedContour

/-! The entire actual angle/angle spectral variation has zero
weighted period on every actual prescribed action circle. This
retains all cycle indices and the native Miura energy shift. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P Q : HillProductEquationPatch} {n m : ℕ+}

theorem completePhasePair_action_Gardner_of_real
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (k : ℕ+) (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) :
    NLS.Poisson.hminusGardnerBracket (C.completePhasePairBracket D) (hillHminusCanonicalAction k) q = 0 := by
  obtain ⟨r,hrpos,_,_,hbr⟩ := C.exists_local_completePhasePair_action_stationary D q hqC hqD hr
  exact (hbr k q (mem_ball_self hrpos)).1

theorem completePhasePairDiscriminant_prescribed_period_eq_zero
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (k : ℕ+) (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) :
    (∮ z in C((P.centers ((k:ℕ):ℤ):ℂ),P.radii ((k:ℕ):ℤ)),
      (z/sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi q) z)*
        C.completePhasePairDiscriminantBracket D q
          (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))) = 0 := by
  have he := P.functional_action_prescribed_circle k (C.completePhasePairBracket D) q (C.subset hqC).1 hr
  rw [C.completePhasePair_action_Gardner_of_real D k q hqC hqD hr] at he
  have hc : -(2*(Real.pi:ℂ)⁻¹) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (by norm_num) (inv_ne_zero (by exact_mod_cast Real.pi_ne_zero)))
  exact (mul_eq_zero.mp he.symm).resolve_left hc

end NLS.KdV.HillPhysicalOnIndexPhaseChart
