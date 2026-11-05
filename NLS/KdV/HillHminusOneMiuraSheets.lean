import NLS.KdV.HillHminusOneNLSMovingSheets
import NLS.KdV.MiuraRealSource
import NLS.SequenceSpaces.PeriodOneMiuraReality

/-! # Exact physical Hill/Dirac sheets for rough shifted Miura images

The source path s*u has the nonlinear actual Hill image Miura(s*u)-s²*c
and the moving energy z²-s²*c. All potentials on this path are real.
The free normalization fixes BOTH the root sign and logarithm period.
No high-frequency or noncollapsed-gap assumption is used.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

theorem hillHminus_shifted_miura_sheets
    (u : PeriodOneRealL2) (q : PeriodOneHminusOne) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    hillHminusContinuedRoot (z^2-(c : ℂ),q) =
      sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraRealSource u).val z ∧
    hillHminusContinuedPrimitive (z^2-(c : ℂ),q) =
      sourceAbelianPrimitive (by simp) (by norm_num) (hillMiuraRealSource u).val
        (hillMiuraRealSource u).property z := by
  let v : ℝ → Coeff 2 := fun s => (s : ℂ) • u.val
  let ψ : ℝ → realTypeSourceSubmodule 2 := fun s => s • hillMiuraRealSource u
  let Q : ℝ → PeriodOneHminusOne := fun s => periodOneMiura (v s)-
    periodOneL2Inclusion (lp.single 2 0 (((s^2*c : ℝ)) : ℂ))
  let E : ℝ → ℂ := fun s => z^2-((s^2*c : ℝ) : ℂ)
  have hv : Continuous v := Complex.continuous_ofReal.smul continuous_const
  have hψ : Continuous ψ := by dsimp [ψ]; fun_prop
  have hψ0 : ψ 0 = 0 := zero_smul ℝ _
  have hsingle : Continuous (fun s : ℝ => (lp.single 2 (0 : ℤ) ((s^2*c : ℝ) : ℂ) : Coeff 2)) :=
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp
      (show Continuous (fun s : ℝ => ((s^2*c : ℝ) : ℂ)) from
        Complex.continuous_ofReal.comp ((continuous_id.pow 2).mul continuous_const))
  have hQ : Continuous Q :=
    (continuous_periodOneMiura.comp hv).sub (periodOneL2Inclusion.continuous.comp hsingle)
  have hQ0 : Q 0 = 0 := by
    simp [Q,v,periodOneMiura,periodOneShiftedMiura]
  have hQr (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1) : IsRealPeriodOneHminusOne (Q s) := by
    apply (periodOneMiura_real (v s) ?_).sub (periodOneL2Inclusion_single_zero_real (s^2*c))
    intro k
    change (s : ℂ)*u.val (-k) = conj ((s : ℂ)*u.val k)
    rw [u.property k,map_mul,conj_ofReal]
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hEi (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1) : (E s).im ≠ 0 := by
    have hz2 : (z^2).im ≠ 0 := by
      simp only [pow_two,mul_im]
      intro he
      apply mul_ne_zero (ne_of_gt hzr) hzi
      nlinarith
    simpa only [E,sub_im,ofReal_im,sub_zero] using hz2
  have hE0 : E 0 = z^2 := by simp [E]
  have hdiag (s : ℝ) : hillMiuraDiagonal (v s) = (ψ s).val := by
    change hillMiuraDiagonal ((s : ℂ) • u.val) = (s : ℂ) • hillMiuraDiagonal u.val
    exact map_smul hillMiuraDiagonal (s : ℂ) u.val
  have htrace (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1) : hillHminusDiscriminant (Q s) (E s) =
      canonicalDiscriminant (by simp) (periodOnePotential (ψ s).val) z := by
    have hi : periodOneMiura (v s) = Q s+periodOneL2Inclusion (lp.single 2 0 ((s^2*c : ℝ) : ℂ)) := by
      dsimp only [Q]
      abel
    have hh := hillHminusDiscriminant_shifted_miura_square (Q s) (v s) ((s^2*c : ℝ) : ℂ) z hi
    rw [hdiag s] at hh
    exact hh
  have hQ1 : Q 1 = q := by
    dsimp only [Q,v]
    rw [ofReal_one,one_smul,himage]
    simp
  have hE1 : E 1 = z^2-(c : ℂ) := by simp [E]
  have hψ1 : ψ 1 = hillMiuraRealSource u := one_smul ℝ _
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num,le_rfl⟩
  have hroot := hillHminusContinuedRoot_eq_NLS_along_energy_path ψ hψ hψ0 Q hQ hQ0 hQr E hE hEi
    z hzr hzi hE0 htrace h1
  have hprimitive := hillHminusContinuedPrimitive_eq_NLS_along_energy_path ψ hψ hψ0 Q hQ hQ0 hQr E hE hEi
    z hzr hzi hE0 htrace h1
  dsimp only at hroot hprimitive
  rw [hQ1,hE1,hψ1] at hroot hprimitive
  exact ⟨hroot,hprimitive⟩

end NLS.KdV
