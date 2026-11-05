import NLS.Fourier.PeriodicPhysicalSourceClosed

/-! The physical REAL mean-zero period-one locus, with its ORIGINAL
Sobolev Fourier-Lebesgue norm, is a closed real Banach subspace at
every real order and every Banach exponent, including p=1. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest PeriodicFourierLebesgue
variable (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

instance realSobolevNormedSpace : NormedSpace ℝ (FourierLebesgueSpace (2:ℝ) s p) :=
  NormedSpace.restrictScalars ℝ ℂ _

def realPeriodOneSobolevSubmodule : Submodule ℝ (FourierLebesgueSpace (2:ℝ) s p) where
  carrier := {q | q.val.IsRealMeanZeroPeriodOne}
  zero_mem' := by
    apply (Distribution.isRealMeanZeroPeriodOne_iff_coefficients _).mpr
    exact ⟨rfl,fun n => (map_zero (starRingEnd ℂ)).symm,fun k => rfl⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha0,har,hap⟩ := (Distribution.isRealMeanZeroPeriodOne_iff_coefficients _).mp ha
    obtain ⟨hb0,hbr,hbp⟩ := (Distribution.isRealMeanZeroPeriodOne_iff_coefficients _).mp hb
    apply (Distribution.isRealMeanZeroPeriodOne_iff_coefficients _).mpr
    refine ⟨?_,?_,?_⟩
    · change a.val (mode 0)+b.val (mode 0)=0
      rw [ha0,hb0,add_zero]
    · intro n
      change a.val (mode n)+b.val (mode n)=star (a.val (mode (-n))+b.val (mode (-n)))
      exact (congrArg₂ (fun x y : ℂ => x+y) (har n) (hbr n)).trans
        (map_add (starRingEnd ℂ) (a.val (mode (-n))) (b.val (mode (-n)))).symm
    · intro k
      change a.val (mode (-(2*k+1)))+b.val (mode (-(2*k+1)))=0
      rw [hap,hbp,add_zero]
  smul_mem' := by
    intro r a ha
    obtain ⟨ha0,har,hap⟩ := (Distribution.isRealMeanZeroPeriodOne_iff_coefficients _).mp ha
    apply (Distribution.isRealMeanZeroPeriodOne_iff_coefficients _).mpr
    refine ⟨?_,?_,?_⟩
    · change (r:ℂ)*a.val (mode 0)=0
      rw [ha0,mul_zero]
    · intro n
      change (r:ℂ)*a.val (mode n)=star ((r:ℂ)*a.val (mode (-n)))
      exact (congrArg (fun z : ℂ => (r:ℂ)*z) (har n)).trans
        ((map_mul (starRingEnd ℂ) (r:ℂ) (a.val (mode (-n)))).trans
          (congrArg (fun z : ℂ => z*star (a.val (mode (-n)))) (Complex.conj_ofReal r))).symm
    · intro k
      change (r:ℂ)*a.val (mode (-(2*k+1)))=0
      rw [hap,mul_zero]

theorem isClosed_realPeriodOneSobolevSubmodule :
    IsClosed (realPeriodOneSobolevSubmodule s p : Set (FourierLebesgueSpace (2:ℝ) s p)) :=
  isClosed_realMeanZeroPeriodOneSource s p

instance realPeriodOneSobolev_complete : CompleteSpace (realPeriodOneSobolevSubmodule s p) :=
  (isClosed_realPeriodOneSobolevSubmodule s p).completeSpace_coe

theorem realPeriodOneSobolev_zero_coefficient (q : realPeriodOneSobolevSubmodule s p) : q.val.val (mode 0)=0 :=
  q.property.2.1

theorem realPeriodOneSobolev_real_coefficient (q : realPeriodOneSobolevSubmodule s p) (n : ℤ) :
    q.val.val (mode n)=star (q.val.val (mode (-n))) :=
  ((Distribution.isRealMeanZeroPeriodOne_iff_coefficients _).mp q.property).2.1 n

theorem realPeriodOneSobolev_odd_coefficient (q : realPeriodOneSobolevSubmodule s p) (n : ℤ) :
    q.val.val (mode (-(2*n+1)))=0 :=
  ((Distribution.isRealMeanZeroPeriodOne_iff_coefficients _).mp q.property).2.2 n

end NLS.Fourier
