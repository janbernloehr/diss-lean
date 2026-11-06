import NLS.Articles.KdVKdV2Frequencies.GlobalRoughGroundActionTails
import NLS.ZakharovShabat.SourceHilbertActionTailCompactness

/-! # Actual rough compactness from one weak coefficient majorant

The uniform original action-tail comparison gives a single summable
ordinary-action majorant. Actual Dirac action properness and continuous
normalized Miura reconstruction produce genuine strong rough compactness.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- A native weak norm bound and ONE Hilbert majorant of the SAME positive
coordinates put ALL actual physical mean-zero preimages in a norm-compact
H-minus-one set. Growing spectral supports are allowed. -/
theorem exists_compact_physical_preimage_container_of_positive_majorant
    (D : GlobalRoughAbelianForwardData) (R : ℝ) (a : Coeff 2) :
    ∃ K : Set PeriodOneHminusOne, IsCompact K ∧
      ∀ p : hillRealMeanZeroSourceSubmodule,
        ‖D.signed (hillOriginalHminusSource p.val.val)‖≤R →
        (∀ j : ℤ, ‖D.positive (hillOriginalHminusSource p.val.val) j‖≤‖a j‖) →
        hillOriginalHminusSource p.val.val∈K := by
  let E := (2/Real.pi)*R^2
  let T := 2*(E+1)
  obtain ⟨N,_hN,htail⟩ := D.exists_uniform_ground_ordinary_signed_action_bound T
  let c : RealCoeff 1 := (2/Real.pi) • Coeff.reCLM 1
    (Coeff.doublingProduct a (star a)+Coeff.doublingProduct (Coeff.reflection a) (star (Coeff.reflection a)))
  have hc (j : ℤ) : c j=(2/Real.pi)*(‖a j‖^2+‖a (-j)‖^2) := by
    change (2/Real.pi)*((a j*star (a j)+a (-j)*star (a (-j))).re)=_
    simp only [Complex.star_def,Complex.mul_conj,Complex.add_re,ofReal_re,Complex.normSq_eq_norm_sq]
  have hcpos (j : ℤ) : 0≤c j := by rw [hc]; positivity
  obtain ⟨C,hC,hcontains⟩ := exists_compact_source_container_of_bounded_action_tail T N c hcpos
  let F : realTypeSourceSubmodule 2 → PeriodOneHminusOne := fun φ =>
    periodOneMiura φ.val.fst-periodOneL2Inclusion (lp.single 2 0 (‖φ.val.fst‖^2 : ℂ))
  have hfst : Continuous (fun φ : realTypeSourceSubmodule 2 => φ.val.fst) :=
    (WithLp.continuous_fst _ _ _).comp continuous_subtype_val
  have hF : Continuous F := (continuous_periodOneMiura.comp hfst).sub
    (periodOneL2Inclusion.continuous.comp
      ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp
        ((continuous_ofReal.comp hfst.norm).pow 2)))
  refine ⟨F '' C,hC.image hF,?_⟩
  intro p hp ha
  let q := hillOriginalHminusSource p.val.val
  let p' : RealPeriodOneHillPotential := ⟨p.val.val,p.val.property⟩
  have hr : IsRealPeriodOneHminusOne q := hillOriginalHminusSource_real _ p.val.property.2
  have hm : q.val 0=0 := by
    rw [hillOriginalHminusSource_zero_mode]
    exact (mem_hillRealMeanZeroSourceSubmodule _).mp p.property
  obtain ⟨u,hu,hi,hn,_ht,_hl,_hr,_ha⟩ := exists_periodOneMiura_ground_factor q hr hm
  have he := D.ground_factor_norm_sq_le_signed_norm q hr hm u hu _ hi
  have heR : ‖u.val‖^2≤E := he.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hp 2) (by positivity))
  have hub : ‖u.val‖≤E+1 := by nlinarith [sq_nonneg (‖u.val‖-1)]
  have hnorm := WithLp.prod_norm_sq_eq_of_L2 (hillMiuraDiagonal u.val)
  rw [hillMiuraDiagonal_fst,hillMiuraDiagonal_snd] at hnorm
  have hpair : ‖hillMiuraDiagonal u.val‖≤T := by
    have hE : 0≤E := by dsimp only [E]; positivity
    dsimp only [T]
    nlinarith [norm_nonneg (hillMiuraDiagonal u.val),norm_nonneg u.val]
  have haction (j : ℤ) (hj : N≤j.natAbs) :
      (sourceRealAction (by simp) (by norm_num) (hillMiuraRealSource u).val (hillMiuraRealSource u).property j).re≤c j := by
    have h := htail p' u _ hu hi hpair j hj
    rw [hc]
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (ha j) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (ha (-j)) 2)) (by positivity))
  refine ⟨hillMiuraRealSource u,hcontains _ hpair haction,?_⟩
  dsimp only [F,hillMiuraRealSource]
  rw [hillMiuraDiagonal_fst]
  rw [←hn] at hi
  have hi' : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 (‖u.val‖^2 : ℂ)) := by
    simpa only [ofReal_pow] using hi
  rw [hi',add_sub_cancel_right]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
