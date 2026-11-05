import NLS.MKdV.MiuraL2CartesianSequence
import NLS.MKdV.MiuraL2ActionSequence
import NLS.SequenceSpaces.WeightedHilbertProduct

/-! # Exact action recovery from the full Cartesian map

The weighted Hilbert product gives a continuous quadratic radius map
into the complete native weighted summable action space. Its composition
with the actual Cartesian sequence is the original physical action map,
including at all closed actions.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraL2CartesianTarget :=
  WeightedCoeff (Weight.sobolev (1/2)) 2 × WeightedCoeff (Weight.sobolev (1/2)) 2

def miuraL2CartesianActions (z : MiuraL2CartesianTarget) : WeightedCoeff (Weight.sobolev 1) 1 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).symm
    (WeightedCoeff.weightIsometry ((Weight.sobolev (1/2)).product (Weight.sobolev (1/2))) 1
      ((1/2 : ℂ) • (WeightedCoeff.hilbertProduct _ _ z.1 z.1+WeightedCoeff.hilbertProduct _ _ z.2 z.2)))

/-- The native quadratic action map has exactly the raw half-radius coefficients. -/
theorem miuraL2CartesianActions_apply (z : MiuraL2CartesianTarget) (n : ℤ) :
    (miuraL2CartesianActions z).val n = (1/2 : ℂ)*((z.1.val n)^2+(z.2.val n)^2) := by
  have hw : (Weight.sobolev (1/2) n)*(Weight.sobolev (1/2) n) = Weight.sobolev 1 n := by
    rw [Weight.sobolev_apply,← Real.rpow_add (by positivity)]
    norm_num
  change (((Weight.sobolev (1/2) n*Weight.sobolev (1/2) n : ℝ) : ℂ)*
    ((1/2 : ℂ)*((WeightedCoeff.hilbertProduct _ _ z.1 z.1).val n+
      (WeightedCoeff.hilbertProduct _ _ z.2 z.2).val n)))/(Weight.sobolev 1 n : ℂ) = _
  rw [hw,WeightedCoeff.hilbertProduct_apply,WeightedCoeff.hilbertProduct_apply,
    mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero n)]
  ring

theorem analyticOnNhd_miuraL2CartesianActions : AnalyticOnNhd ℂ miuraL2CartesianActions univ := by
  intro z _
  have hx := ((WeightedCoeff.analyticOnNhd_hilbertProduct (Weight.sobolev (1/2)) (Weight.sobolev (1/2)))
    (z.1,z.1) (mem_univ _)).comp (f := fun v : MiuraL2CartesianTarget => (v.1,v.1))
      (analyticAt_fst.prod analyticAt_fst)
  have hy := ((WeightedCoeff.analyticOnNhd_hilbertProduct (Weight.sobolev (1/2)) (Weight.sobolev (1/2)))
    (z.2,z.2) (mem_univ _)).comp (f := fun v : MiuraL2CartesianTarget => (v.2,v.2))
      (analyticAt_snd.prod analyticAt_snd)
  have hc : AnalyticAt ℂ (fun _ : MiuraL2CartesianTarget => (1/2 : ℂ)) z := analyticAt_const
  have hpoly : AnalyticAt ℂ (fun v : MiuraL2CartesianTarget => (1/2 : ℂ) •
      (WeightedCoeff.hilbertProduct _ _ v.1 v.1+WeightedCoeff.hilbertProduct _ _ v.2 v.2)) z := by
    simpa only [Function.comp_def,Pi.add_apply,Pi.smul_apply] using! hc.smul (hx.add hy)
  exact (((WeightedCoeff.weightIsometry (Weight.sobolev 1) 1).symm.toContinuousLinearEquiv.analyticAt _).comp
    (((WeightedCoeff.weightIsometry ((Weight.sobolev (1/2)).product (Weight.sobolev (1/2))) 1).toContinuousLinearEquiv.analyticAt _).comp
      hpoly))

theorem continuous_miuraL2CartesianActions : Continuous miuraL2CartesianActions :=
  continuous_iff_continuousAt.mpr (fun z => (analyticOnNhd_miuraL2CartesianActions z (mem_univ _)).continuousAt)

/-- The full quadratic radii are the actual original L² action sequence. -/
theorem miuraL2CartesianActions_sequence_eq (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    miuraL2CartesianActions (miuraL2CartesianSequence a) = miuraL2ActionSequence a := by
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraL2CartesianSequence_domain
  obtain ⟨V,_,hrealV,_,hact⟩ := exists_miuraL2ActionSequence_domain
  apply Subtype.ext
  funext n
  have he := hcoord a (hreal ha) n
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change (miuraL2CartesianSequence a).1.val n = (miuraL2CartesianCoefficient a n).1 at hx
  change (miuraL2CartesianSequence a).2.val n = (miuraL2CartesianCoefficient a n).2 at hy
  rw [miuraL2CartesianActions_apply,hx,hy]
  by_cases hn : 0 < n
  · have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
    have hnat : 1 ≤ n.toNat := by omega
    rw [miuraL2CartesianCoefficient,if_pos hn,miuraL2CartesianCoordinates_radius a ha n.toNat hnat]
    have haction := hact a (hrealV ha) n.toNat hnat
    rw [hi] at haction
    rw [haction]
    ring
  · rw [miuraL2CartesianCoefficient,if_neg hn,miuraL2ActionSequence_nonpositive a n hn]
    norm_num

end NLS.MKdV
