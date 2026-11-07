import NLS.KdV.HillCompletePhaseDiscriminant
import NLS.KdV.HillRealDiagonalCartesian

/-! Every actual on-index phase chart is real on the physical real
source form. Its doubled exponential is the actual unit-modulus
physical phase square, so no choice of a real phase representative
is assumed. The complete intrinsic correction preserves reality. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem original_gap_ne_zero_of_real (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCanonicalGapSquare n q ≠ 0 := by
  intro hg
  have hG := P.frequency_gap_zero_of_real_original_gap_zero n q (C.subset hq).1 hr hg
  have hd := (C.identities q hq).1
  rw [hG] at hd
  have hz : C.halfGap q^2=0 := by simpa using hd
  exact C.halfGap_ne q hq (eq_zero_of_pow_eq_zero hz)

theorem phase_im_eq_zero_of_real (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    (C.phase q).im = 0 := by
  have hg := C.original_gap_ne_zero_of_real q hq hr
  obtain ⟨a,hp,hm⟩ := P.exists_real_original_diagonal_phase n q (C.subset hq).1 hr hg
  have heq : ‖P.physicalOnIndexCartesianPlus n q‖=‖P.physicalOnIndexCartesianMinus n q‖ := by
    rw [hp,hm,norm_mul,norm_mul]
    simp [Complex.norm_exp,Complex.mul_re]
  have hne : ‖P.physicalOnIndexCartesianMinus n q‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (P.physicalOnIndexCartesian_ne_zero_of_original_gap n q (C.subset hq) hg).2
  rcases C.identities q hq with ⟨_,hpoint,hroot,hphase,_⟩
  have hs := P.physicalOnIndexPhaseSquare_eq_exp_on_cover n q (C.subset hq) hg
    (C.halfGap q) (C.angle q) hpoint hroot
  rw [← hphase] at hs
  have hu : ‖Complex.exp (2*I*C.phase q)‖=1 := by
    rw [← hs,HillProductEquationPatch.physicalOnIndexPhaseSquare,norm_div,heq,div_self hne]
  rw [Complex.norm_exp] at hu
  have hz : (2*I*C.phase q).re=0 := Real.exp_injective (by simpa only [Real.exp_zero] using hu)
  norm_num [Complex.mul_re,Complex.mul_im] at hz
  linarith

theorem completePhase_im_eq_zero_of_real (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    (C.completePhase q).im = 0 := by
  simp only [completePhase,add_im,C.phase_im_eq_zero_of_real q hq hr,
    hillHminusOffIndexAbelianCorrection_im_eq_zero_of_real n q hr,add_zero]

end NLS.KdV.HillPhysicalOnIndexPhaseChart
