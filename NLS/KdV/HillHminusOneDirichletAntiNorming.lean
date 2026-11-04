import NLS.KdV.HillHminusOneDirichletMiuraLabels
import NLS.KdV.HillHminusOneDirichletLogNorming
import NLS.MKdV.L2QuasiHillNormingGauge
import NLS.ComplexAnalysis.RealArsinhExtension

/-! # Actual anti-discriminant samples recover the logarithmic Hill norming data

The exact all-index Miura correspondence fixes the terminal multiplier.
The signed half anti-discriminant equals sinh of the real logarithmic
norming constant; principal inverse sinh recovers it without phase choices.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open MeasureTheory hiding extend
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

theorem HillHminusMiuraChart.dirichlet_antiDiscriminant_eq_norming
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealPeriodOneHminusOne q) (c : ℝ) (hc : C.energyShift = (c : ℂ)^2)
    (hreal : star (C.physicalProfile q) = C.physicalProfile q) (n : ℕ+) :
    sourceAntiDiscriminantCandidate (by simp) (by norm_num) (hillDirichletMiuraSource (C.lift q))
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
        (hillDirichletMiuraSource (C.lift q)) (n : ℤ)) =
      hillHminusDirichletNorming q hr n-(hillHminusDirichletNorming q hr n)⁻¹ := by
  let P := hillDirichletMiuraSource (C.lift q)
  let z := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet P (n : ℤ)
  have hzpos : 0 < z.re := (canonicalDirichletMiuraRoot_re_pos_iff (C.lift q)
    (C.lift_real_of_profile_real q hreal) (n : ℤ)).mpr (by exact_mod_cast n.property)
  have hz : z ≠ 0 := by intro h; rw [h,zero_re] at hzpos; exact lt_irrefl _ hzpos
  have hzero : periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet P z = 0 := by
    apply (periodOneBoundaryCharacteristic_eq_zero_iff (by simp) (by norm_num) .dirichlet P _).mpr
    exact (canonicalPeriodOneBoundaryRoots_exhaustive (by simp) (by norm_num) .dirichlet P _).mpr ⟨(n : ℤ),rfl⟩
  have hpzero : l2SeparatedCharacteristic .dirichlet (intervalL2DirichletMiura (C.physicalProfile q)) z = 0 := by
    rw [periodOneBoundaryCharacteristic_eq_l2,sourcePhysicalL2_hillDirichletMiuraSource] at hzero
    exact hzero
  have henergy : (hillHminusDirichletEnergy q hr n : ℂ)+C.energyShift = z^2 := by
    rw [C.dirichletEnergy_eq_source_root_sq q hq hr c hc hreal n,sub_add_cancel]
  have hnorm : hillHminusDirichletNorming q hr n =
      extend (l2QuasiHillMomentum (C.physicalProfile q) (z^2) (0,1)) 1 := by
    rw [hillHminusDirichletNorming_eq_chart C q hq hr n]
    change extend (l2QuasiHillMomentum (C.physicalProfile q)
      ((hillHminusDirichletEnergy q hr n : ℂ)+C.energyShift) (0,1)) 1 = _
    rw [henergy]
  change sourceAntiDiscriminantCandidate (by simp) (by norm_num) P z = _
  rw [sourceAntiDiscriminantCandidate_eq_l2,sourcePhysicalL2_hillDirichletMiuraSource,hnorm]
  exact l2AntiDiscriminant_dirichletMiura (C.physicalProfile q) z hz hpzero

theorem signed_half_norming_difference_eq_sinh (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (-1 : ℂ)^(n : ℕ)*(hillHminusDirichletNorming q hr n-
      (hillHminusDirichletNorming q hr n)⁻¹)/2 =
      (Real.sinh (hillHminusDirichletLogNorming q hr n) : ℂ) := by
  let s : ℝ := (-1)^(n : ℕ)
  let w := hillHminusDirichletNorming q hr n
  have hs : s^2 = 1 := by dsimp [s]; rw [← pow_mul,Nat.mul_comm (n : ℕ) 2,pow_mul]; norm_num
  have hw : (w.re : ℂ) = w := by
    apply Complex.ext
    · rfl
    · exact (hillHminusDirichletNorming_real q hr n).symm
  have he := exp_hillHminusDirichletLogNorming q hr n
  change Real.exp (hillHminusDirichletLogNorming q hr n) = s*w.re at he
  rw [Real.sinh_eq,Real.exp_neg,he]
  have heq : s*(w.re-w.re⁻¹)/2 = (s*w.re-(s*w.re)⁻¹)/2 := by
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_left (by nlinarith [hs])
    rw [mul_inv_rev,hsi]
    ring
  have hcast := congrArg (fun x : ℝ => (x : ℂ)) heq
  push_cast at hcast ⊢
  simpa only [s,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one,hw,w] using hcast

theorem realArsinhExtension_signed_half_norming_difference (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    NLS.ComplexAnalysis.realArsinhExtension
      ((-1 : ℂ)^(n : ℕ)*(hillHminusDirichletNorming q hr n-
        (hillHminusDirichletNorming q hr n)⁻¹)/2) =
      (hillHminusDirichletLogNorming q hr n : ℂ) := by
  rw [signed_half_norming_difference_eq_sinh,NLS.ComplexAnalysis.realArsinhExtension_ofReal,Real.arsinh_sinh]

end NLS.KdV
