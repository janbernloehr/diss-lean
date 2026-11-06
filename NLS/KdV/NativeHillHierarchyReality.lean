import NLS.KdV.NativeHillHierarchyIsospectral
import NLS.KdV.NativeHamiltonianReality
import NLS.ZakharovShabat.SobolevOddHamiltonianReal

/-! # Reality of every original native scalar KdV Hamiltonian

The actual real Miura trace fixes the imaginary part at the common ground
shift. The native constant-direction identity and induction show that the
imaginary part is constant on all real constant shifts.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.MKdV
open scoped ComplexConjugate
namespace NLS.KdV

/-- The actual physical quadratic mass is real at every native order. -/
theorem nativeMiuraMass_im_eq_zero (s : ℕ) (q : ScalarSobolev s)
    (hq : ∀ n : ℤ, q.val (-n) = conj (q.val n)) : (nativeMiuraMass s q).im = 0 := by
  let q₀ := hierarchySobolevInclusion s 0 (by omega) q
  have hq₀ (n : ℤ) : q₀.val (-n) = conj (q₀.val n) := by
    simpa only [q₀,hierarchySobolevInclusion_apply] using hq n
  have he : nativeMiuraMass s q = (1/2 : ℂ)*nativeTopJetSquare 0 q₀ := rfl
  rw [he,nativeTopJetSquare_eq_norm_sq 0 q₀ hq₀]
  norm_num [Complex.mul_im,Complex.div_im]
  simp only [←Complex.ofReal_pow,Complex.ofReal_im]

/-- The independently defined native Miura hierarchy is real on every
physically real factor, by the actual full odd Hamiltonian trace. -/
theorem nativeMiuraHillHamiltonian_im_eq_zero (s : ℕ) (hs : 1 ≤ s) (u : ScalarSobolev s)
    (hu : ∀ n : ℤ, u.val (-n) = conj (u.val n)) : (nativeMiuraHillHamiltonian s u).im = 0 := by
  let a : realTypeHigherSobolevSourceLocus s := ⟨(u,u),by
    rw [higherSobolevSourceInclusion_diagonal_eq s u hu]
    exact (hillMiuraRealSource (nativeRealMiuraFactor s u hu)).property⟩
  have h := sobolevOddHamiltonian_im_zero s hs a
  change (sobolevOddHamiltonian s hs (u,u)).im = 0 at h
  rw [nativeMiuraHillHamiltonian_odd_restriction] at h
  norm_num [Complex.mul_im] at h
  linarith

/-- Every real constant shift of every original real mean-zero native
source has a real physical hierarchy value, at every order. -/
theorem nativeHillHierarchyHamiltonian_shift_im_eq_zero (m : ℕ) :
    ∀ q : ScalarSobolev m, (∀ n : ℤ, q.val (-n) = conj (q.val n)) → q.val 0 = 0 →
      ∀ c : ℝ, (nativeHillHierarchyHamiltonian m (q+(c : ℂ) • nativeScalarConstant m 1)).im = 0 := by
  induction m with
  | zero =>
    intro q hq hqm c
    rw [nativeHillHierarchyHamiltonian_zero,smul_nativeScalarConstant,mul_one,
      nativeMiuraMass_add_constant,hqm,mul_zero,add_zero]
    norm_num [Complex.add_im,Complex.div_im,nativeMiuraMass_im_eq_zero 0 q hq]
    simp only [←Complex.ofReal_pow,Complex.ofReal_im]
  | succ m ih =>
    intro q hq hqm c
    obtain ⟨u,hu,hmu,hi,_⟩ := exists_nativeMiura_ground_factor (m+1) (nativeHillSource (m+1) q)
      (nativeHillSource_real (m+1) q hq)
      (by simpa only [nativeHillSource_apply] using hqm) (nativeHillSource_regular (m+1) q)
    let e : ℝ := -hillHminusLowestRealRoot (nativeHillSource (m+1) q) (nativeHillSource_real (m+1) q hq)
    have hE : (nativeHillHierarchyHamiltonian (m+1) (q+(e : ℂ) • nativeScalarConstant (m+1) 1)).im = 0 := by
      rw [smul_nativeScalarConstant,mul_one,
        ←nativeMiuraPotential_eq_add_constant (m+1) q u hu (e : ℂ) hi,
        nativeHillHierarchyHamiltonian_miura]
      exact nativeMiuraHillHamiltonian_im_eq_zero (m+2) (by omega) u hu
    let F : ℝ → ℝ := fun d => (nativeHillHierarchyHamiltonian (m+1)
      (q+(d : ℂ) • nativeScalarConstant (m+1) 1)).im
    have hd (d : ℝ) : HasDerivAt F 0 d := by
      have h := (hasDerivAt_nativeHillHierarchyHamiltonian_shift m q (d : ℂ)).comp_ofReal
      have h' := Complex.imCLM.hasFDerivAt.comp_hasDerivAt d h
      have hlow := ih (hierarchySobolevInclusion (m+1) m (by omega) q)
        (by simpa only [hierarchySobolevInclusion_apply] using hq)
        (by simpa only [hierarchySobolevInclusion_apply] using hqm) d
      have hz : Complex.imCLM (2*((2*m+3 : ℕ) : ℂ)*nativeHillHierarchyHamiltonian m
          (hierarchySobolevInclusion (m+1) m (by omega) q+(d : ℂ) • nativeScalarConstant m 1)) = 0 := by
        change (2*((2*m+3 : ℕ) : ℂ)*nativeHillHierarchyHamiltonian m
          (hierarchySobolevInclusion (m+1) m (by omega) q+(d : ℂ) • nativeScalarConstant m 1)).im = 0
        rw [Complex.mul_im,hlow]
        norm_num [Complex.mul_im]
      rw [hz] at h'
      exact h'
    exact (is_const_of_deriv_eq_zero (fun d => (hd d).differentiableAt) (fun d => (hd d).deriv) c e).trans hE

/-- Every original native physical hierarchy member takes real values on
its entire original real mean-zero H^m source domain. -/
theorem nativeHillHierarchyHamiltonian_im_eq_zero (m : ℕ) (q : ScalarSobolev m)
    (hq : ∀ n : ℤ, q.val (-n) = conj (q.val n)) (hqm : q.val 0 = 0) :
    (nativeHillHierarchyHamiltonian m q).im = 0 := by
  simpa only [ofReal_zero,zero_smul,add_zero] using
    nativeHillHierarchyHamiltonian_shift_im_eq_zero m q hq hqm 0

end NLS.KdV
