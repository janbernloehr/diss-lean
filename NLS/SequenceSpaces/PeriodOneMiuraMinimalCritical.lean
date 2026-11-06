import NLS.SequenceSpaces.PeriodOneMiuraMinimalEnergy
import NLS.SequenceSpaces.PeriodOneRealMiuraLocalInverse

/-! # Every actual least-energy real Miura factor is critical

A real local inverse would produce genuine factors at strictly smaller
energies. Fredholm compactness supplies a nonzero literal Fourier kernel.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

theorem not_bijective_periodOneMiuraDerivative_of_minimal
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (e : ℝ) (u : PeriodOneRealL2)
    (hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hmin : ∀ (f : ℝ) (v : PeriodOneRealL2),
      periodOneMiura v.val = q+periodOneL2Inclusion (lp.single 2 0 (f : ℂ)) → e ≤ f) :
    ¬Function.Bijective (periodOneMiuraFrechetDerivative u.val) := by
  intro hb
  obtain ⟨W,hW,huW,g,_hga,_hbase,hg⟩ := exists_real_periodOneMiura_inverse_of_bijective u hb
  let L : ℝ → PeriodOneHminusOne := fun f => q+periodOneL2Inclusion (lp.single 2 0 (f : ℂ))
  have hL : Continuous L := continuous_const.add (periodOneL2Inclusion.continuous.comp
    ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp continuous_ofReal))
  have heW : e ∈ L ⁻¹' W := by change L e ∈ W; rw [show L e = periodOneMiura u.val from hu.symm]; exact huW
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp (hW.preimage hL) e heW
  let f := e-δ/2
  have hfW : L f ∈ W := by
    apply hball
    rw [mem_ball,Real.dist_eq,show f-e = -(δ/2) from by dsimp [f]; ring,
      abs_neg,abs_of_pos (half_pos hδ)]
    linarith
  have hfr : IsRealPeriodOneHminusOne (L f) := by
    intro j
    change (q+periodOneL2Inclusion (lp.single 2 0 (f : ℂ))).val (-j) =
      conj ((q+periodOneL2Inclusion (lp.single 2 0 (f : ℂ))).val j)
    simp only [WeightedCoeff.add_val,map_add]
    rw [hr j,periodOneL2Inclusion_single_zero_real f j]
  let v : PeriodOneRealL2 := ⟨g (L f),(hg (L f) hfW).2 hfr⟩
  have hle : e ≤ f := hmin f v (hg (L f) hfW).1
  dsimp [f] at hle
  linarith

theorem exists_periodOneMiura_kernel_of_minimal
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (e : ℝ) (u : PeriodOneRealL2)
    (hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hmin : ∀ (f : ℝ) (v : PeriodOneRealL2),
      periodOneMiura v.val = q+periodOneL2Inclusion (lp.single 2 0 (f : ℂ)) → e ≤ f) :
    ∃ v : Coeff 2, v ≠ 0 ∧ ∀ j : ℤ,
      2*I*(Real.pi : ℂ)*j*v j+2*(periodOneMiuraProduct u.val v).val j = 0 := by
  obtain ⟨v,hv,he⟩ := exists_periodOneMiura_kernel_of_not_bijective u.val
    (not_bijective_periodOneMiuraDerivative_of_minimal q hr e u hu hmin)
  refine ⟨v,hv,?_⟩
  intro j
  have h := congrArg (fun p : PeriodOneHminusOne => p.val j) he
  simpa only [periodOneMiuraFrechetDerivative_apply,WeightedCoeff.zero_val] using h

end NLS
