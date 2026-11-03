import NLS.KdV.HminusOneHillPsiProductContinuity
import NLS.SequenceSpaces.PeriodOneHminusOneRealDensity

/-! The actual scalar normalization transfers from literal real L2
sources to every real native H-minus-one source by density. The L2
normalization identity is an explicit remaining premise, not an axiom
or a claimed result of this module. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminusPsiProductScalar_eq_const_of_real_L2 (n : ℕ+) (C : ℂ)
    (hL2 : ∀ u : PeriodOneRealL2,
      hillHminusPsiProductScalar n (periodOneRealL2Inclusion u).val (periodOneRealL2Inclusion u).property = C)
    (q : PeriodOneRealHminusOne) : hillHminusPsiProductScalar n q.val q.property = C := by
  have he := denseRange_periodOneRealL2Inclusion.equalizer
    (continuous_hillHminusPsiProductScalar n) (continuous_const (y := C)) (funext hL2)
  exact congrFun he q

theorem hillHminusPsiProductScalar_normalization_iff_real_L2 (n : ℕ+) (C : ℂ) :
    (∀ q : PeriodOneRealHminusOne, hillHminusPsiProductScalar n q.val q.property = C) ↔
      ∀ u : PeriodOneRealL2,
        hillHminusPsiProductScalar n (periodOneRealL2Inclusion u).val (periodOneRealL2Inclusion u).property = C :=
  ⟨fun h u => h (periodOneRealL2Inclusion u),fun h q => hillHminusPsiProductScalar_eq_const_of_real_L2 n C h q⟩

end NLS.KdV
