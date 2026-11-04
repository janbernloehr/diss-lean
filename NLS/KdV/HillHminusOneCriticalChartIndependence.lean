import NLS.KdV.HillHminusOneRealCriticalEnergyGeometry
import Mathlib.Order.WellFounded

/-! # Intrinsic labels of real rough Hill critical energies

Two actual Miura charts enumerate the same complete strictly increasing real
critical spectrum. Consequently their positive energy labels agree on every
real overlap, without restrictions on the size of the potential or its gaps.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV.HillHminusMiuraChart

theorem energyCritical_eq_of_real_overlap (C D : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.domain) (hqD : q ∈ D.domain)
    (hrC : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hrD : IsRealType (CoeffPair.toMax 2 (D.criticalSource q)))
    (hc : C.energyShift.im = 0) (hd : D.energyShift.im = 0) (j : ℕ+) :
    C.energyCritical q j = D.energyCritical q j := by
  have hrange : range (fun n : ℕ+ => (C.energyCritical q n).re) =
      range (fun n : ℕ+ => (D.energyCritical q n).re) := by
    ext x
    constructor
    · rintro ⟨n,rfl⟩
      obtain ⟨m,hm⟩ := (D.energyCritical_exhaustive q hrD hqD _).mp
        (C.energyCritical_is_critical q hrC hqC n)
      exact ⟨m,congrArg Complex.re hm⟩
    · rintro ⟨n,rfl⟩
      obtain ⟨m,hm⟩ := (C.energyCritical_exhaustive q hrC hqC _).mp
        (D.energyCritical_is_critical q hrD hqD n)
      exact ⟨m,congrArg Complex.re hm⟩
  have he := (C.strictMono_energyCritical_re q hrC).range_inj
    (D.strictMono_energyCritical_re q hrD) |>.mp hrange
  apply Complex.ext
  · exact congrFun he j
  · rw [C.energyCritical_im_eq_zero q hrC hc j,D.energyCritical_im_eq_zero q hrD hd j]

end NLS.KdV.HillHminusMiuraChart
