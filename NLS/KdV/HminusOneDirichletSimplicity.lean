import NLS.KdV.HminusOneDirichletOrder
import NLS.ZakharovShabat.SourceAuxiliarySimpleRoots

/-! ALL zeros of the full rough Dirichlet characteristic are simple for
real original H-minus-one potentials. A constructed real Miura lift avoids
the zero square-root energy, including at every low scalar energy. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- Every real-potential Dirichlet zero has analytic multiplicity one.
This includes low energies and collapsed periodic gaps. -/
theorem analyticOrderAt_hillHminusDirichlet_eq_one_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ)
    (hl : hillHminusDirichlet q lambda = 0) :
    analyticOrderAt (hillHminusDirichlet q) lambda = 1 := by
  obtain ⟨c,_,u,hi,hn⟩ := exists_real_periodOneMiura_shift_avoiding q hq lambda
  let z := Complex.sqrt (lambda+(c:ℂ)^2)
  have hsq : z^2 = lambda+(c:ℂ)^2 := NLS.ComplexAnalysis.complex_sqrt_sq _
  have hz : z ≠ 0 := by
    intro he
    apply hn
    rw [← hsq,he]
    norm_num
  have hzero : auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal u.val) z = 0 := by
    rw [auxiliaryDirichlet_eq_mul_hillHminusDirichlet q u.val ((c:ℂ)^2) z hi,
      hsq,add_sub_cancel_right,hl,mul_zero]
  have ho := analyticOrderAt_auxiliaryPeriodOneCharacteristic_eq_one_of_realType
    (by simp) (by norm_num) .dirichlet (hillMiuraDiagonal u.val)
      (isRealType_hillMiuraDiagonal u) z hzero
  have ht := analyticOrderAt_hillHminusDirichlet_shifted_miura q u.val ((c:ℂ)^2) z hi hz
  rw [hsq,add_sub_cancel_right] at ht
  rw [← analyticOrderAt_auxiliaryPeriodOneCharacteristic] at ht
  exact ht.trans ho

theorem analyticOrderNatAt_hillHminusDirichlet_eq_one_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ)
    (hl : hillHminusDirichlet q lambda = 0) :
    analyticOrderNatAt (hillHminusDirichlet q) lambda = 1 := by
  have he := congrArg ENat.toNat (analyticOrderAt_hillHminusDirichlet_eq_one_of_real q hq lambda hl)
  simpa only [analyticOrderNatAt,ENat.toNat_one] using he

/-- The actual full scalar characteristic has nonzero spectral derivative
at every real-potential Dirichlet zero, without a high-energy restriction. -/
theorem deriv_hillHminusDirichlet_ne_zero_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ)
    (hl : hillHminusDirichlet q lambda = 0) : deriv (hillHminusDirichlet q) lambda ≠ 0 := by
  have ha : AnalyticAt ℂ (hillHminusDirichlet q) lambda :=
    (analyticOnNhd_hillHminusDirichlet_joint (lambda,q) (mem_univ _)).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have ho := analyticOrderAt_hillHminusDirichlet_eq_one_of_real q hq lambda hl
  have hd : analyticOrderAt (deriv (hillHminusDirichlet q)) lambda = 0 :=
    analyticOrderAt_deriv_of_pos ha (n := 0) (by simpa using ho)
  intro hz
  exact (ha.deriv.analyticOrderAt_ne_zero.mpr hz) hd

end NLS.KdV
