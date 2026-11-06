import NLS.SequenceSpaces.PeriodOneRealMiuraProperness
import Mathlib.Topology.Order.Monotone

/-! # A least actual real Miura energy shift for every mean-zero rough source

The proper real Miura map has closed image. Its intersection with the
constant-energy line is closed and nonempty, and every admissible energy
equals the squared norm of its actual real factor. The infimum is therefore
attained. No ground-state factor or global inverse is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

def periodOneRealMiuraEnergies (q : PeriodOneHminusOne) : Set ℝ :=
  {e | q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)) ∈ range periodOneRealMiura}

theorem isClosed_periodOneRealMiuraEnergies (q : PeriodOneHminusOne) :
    IsClosed (periodOneRealMiuraEnergies q) := by
  apply isClosed_range_periodOneRealMiura.preimage
  exact continuous_const.add (periodOneL2Inclusion.continuous.comp
    ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp continuous_ofReal))

theorem periodOneRealMiura_energy_eq_norm_sq (q : PeriodOneHminusOne) (hm : q.val 0 = 0)
    (e : ℝ) (u : PeriodOneRealL2)
    (hu : periodOneRealMiura u = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ))) :
    e = ‖u.val‖^2 := by
  have he := congrArg (fun p : PeriodOneHminusOne => p.val 0) hu
  rw [periodOneRealMiura,periodOneMiura_zero_eq_norm_sq u.val u.property] at he
  simpa only [WeightedCoeff.add_val,hm,periodOneL2Inclusion_apply,lp.single_apply,Pi.single_apply,
    if_true,zero_add,ofReal_inj] using he.symm

theorem nonempty_periodOneRealMiuraEnergies (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : (periodOneRealMiuraEnergies q).Nonempty := by
  obtain ⟨c,_hc,_hlarge,V,_hV,hq,u,_hUa,hreal,hsolve⟩ :=
    exists_real_periodOneMiura_large_energyChart q hr 0
  refine ⟨c^2,⟨⟨u q,hreal⟩,?_⟩⟩
  change periodOneMiura (u q) = q+periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ))
  simpa only [ofReal_pow] using hsolve q hq

/-- EVERY real mean-zero rough source has an ACTUAL real L2 factor at
the LEAST admissible constant energy shift. Its squared norm is exactly
that shift. The source need not initially be L2 or close to zero. -/
theorem exists_periodOneMiura_minimal_energy (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    ∃ e : ℝ, 0 ≤ e ∧ ∃ u : PeriodOneRealL2,
      periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)) ∧
      ‖u.val‖^2 = e ∧
      ∀ (f : ℝ) (v : PeriodOneRealL2),
        periodOneMiura v.val = q+periodOneL2Inclusion (lp.single 2 0 (f : ℂ)) → e ≤ f := by
  have hnon := nonempty_periodOneRealMiuraEnergies q hr
  have hbelow : BddBelow (periodOneRealMiuraEnergies q) := by
    refine ⟨0,?_⟩
    rintro e ⟨u,hu⟩
    rw [periodOneRealMiura_energy_eq_norm_sq q hm e u hu]
    positivity
  have hleast := (isClosed_periodOneRealMiuraEnergies q).isLeast_csInf hnon hbelow
  obtain ⟨u,hu⟩ := hleast.1
  have hnorm := periodOneRealMiura_energy_eq_norm_sq q hm _ u hu
  refine ⟨_,by rw [hnorm]; positivity,u,hu,hnorm.symm,?_⟩
  intro f v hv
  exact hleast.2 ⟨v,hv⟩

/-- A genuine real Miura energy controls the actual rough source norm
with UNIVERSAL constants: all operator norms here are fixed, independent
of the source and of the factor. The remaining spectral step is to bound
the minimal energy in terms of the actual weak target actions. -/
theorem norm_source_le_of_realMiura_energy (q : PeriodOneHminusOne) (hm : q.val 0 = 0)
    (e : ℝ) (u : PeriodOneRealL2)
    (hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ))) :
    ‖q‖ ≤ (‖periodOneMassOperator 0‖+‖periodOneL2Inclusion‖)*Real.sqrt e+
      (‖periodOneMiuraProduct‖+‖periodOneL2Inclusion‖)*e := by
  have he : e = ‖u.val‖^2 := periodOneRealMiura_energy_eq_norm_sq q hm e u hu
  have he0 : 0 ≤ e := he.symm ▸ sq_nonneg ‖u.val‖
  have hroot : Real.sqrt e = ‖u.val‖ := by rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hq : q = periodOneMiura u.val-periodOneL2Inclusion (lp.single 2 0 (e : ℂ)) := by
    rw [hu,add_sub_cancel_right]
  have hMiura : ‖periodOneMiura u.val‖ ≤
      ‖periodOneMassOperator 0‖*‖u.val‖+‖periodOneMiuraProduct‖*‖u.val‖*‖u.val‖+
        ‖periodOneL2Inclusion‖*‖u.val‖ := by
    unfold periodOneMiura periodOneShiftedMiura
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ((periodOneMassOperator 0).le_opNorm _)
        (periodOneMiuraProduct.le_opNorm₂ _ _))) (periodOneL2Inclusion.le_opNorm _))
  have hsingle : ‖periodOneL2Inclusion (lp.single 2 0 (e : ℂ))‖ ≤ ‖periodOneL2Inclusion‖*e := by
    simpa only [lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞)),Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg he0] using periodOneL2Inclusion.le_opNorm (lp.single 2 0 (e : ℂ))
  calc
    ‖q‖ ≤ ‖periodOneMiura u.val‖+‖periodOneL2Inclusion (lp.single 2 0 (e : ℂ))‖ := by
      rw [hq]; exact norm_sub_le _ _
    _ ≤ (‖periodOneMassOperator 0‖*‖u.val‖+‖periodOneMiuraProduct‖*‖u.val‖*‖u.val‖+
        ‖periodOneL2Inclusion‖*‖u.val‖)+‖periodOneL2Inclusion‖*e := add_le_add hMiura hsingle
    _ = _ := by rw [hroot,he]; ring

end NLS
