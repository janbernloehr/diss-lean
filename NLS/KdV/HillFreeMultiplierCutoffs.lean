import NLS.KdV.HillFreeInteractionKernel
import NLS.ComplexAnalysis.UniformProductTails

/-! Exact finite-cutoff factorization of the free Hill multiplier.
Every retained factor is its free value times one plus the explicit
interaction perturbation. The deleted and selected labels stay literal. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergySequencePartialProduct_coordinate_difference (n m : ℕ+) (hmn : m ≠ n)
    (N : ℕ) (hN : (m:ℕ) ≤ N) (E : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergySequencePartialProduct n N (E,hillZeroCoordinateShift m d 1)-
      hillEnergySequencePartialProduct n N (E,d) =
    ((m:ℕ)/((Real.pi:ℂ)*(m:ℕ))^2)*
      ∏ j ∈ ((Finset.range N).erase ((n:ℕ)-1)).erase ((m:ℕ)-1),hillEnergySequenceFactor (E,d) j := by
  have hmn' : (m:ℕ)-1 ≠ (n:ℕ)-1 := by
    intro h
    apply hmn
    apply Subtype.ext
    change (m:ℕ) = (n:ℕ)
    have hm := m.pos
    have hn := n.pos
    omega
  have hmem : (m:ℕ)-1 ∈ (Finset.range N).erase ((n:ℕ)-1) := by
    simp only [Finset.mem_erase,Finset.mem_range]
    exact ⟨hmn',by have hm := m.pos; omega⟩
  unfold hillEnergySequencePartialProduct
  rw [← Finset.mul_prod_erase _ (hillEnergySequenceFactor (E,hillZeroCoordinateShift m d 1)) hmem,
    ← Finset.mul_prod_erase _ (hillEnergySequenceFactor (E,d)) hmem]
  have he : (∏ j ∈ ((Finset.range N).erase ((n:ℕ)-1)).erase ((m:ℕ)-1),
      hillEnergySequenceFactor (E,hillZeroCoordinateShift m d 1) j) =
      ∏ j ∈ ((Finset.range N).erase ((n:ℕ)-1)).erase ((m:ℕ)-1),hillEnergySequenceFactor (E,d) j :=
    Finset.prod_congr rfl (fun j hj => hillEnergySequenceFactor_shift_other m E d 1 j (Finset.ne_of_mem_erase hj))
  rw [he,hillEnergySequenceFactor_shift_selected]
  ring

theorem hillEnergySequenceFactor_freeEnergy_interaction (n m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (j : ℕ) (hjn : j ≠ (n:ℕ)-1) (hjm : j ≠ (m:ℕ)-1) :
    hillEnergySequenceFactor ((((Real.pi:ℂ)*(m:ℕ))^2),d) j =
      hillEnergySequenceFactor ((((Real.pi:ℂ)*(m:ℕ))^2),0) j*
        (1+hillFreeInteractionPerturbation n m d j) := by
  let k : ℕ+ := ⟨j+1,by omega⟩
  have hkm : k ≠ m := fun h => hjm ((positive_cutoff_index_eq m j).mp h)
  have hk : ((k:ℕ):ℂ) = (j:ℂ)+1 := by change ((j+1:ℕ):ℂ) = (j:ℂ)+1; simp only [Nat.cast_add,Nat.cast_one]
  have hki : ((k:ℕ):ℤ) = (j:ℤ)+1 := by change ((j+1:ℕ):ℤ) = (j:ℤ)+1; simp only [Nat.cast_add,Nat.cast_one]
  have hu : hillFreeInteractionPerturbation n m d j =
      d k*(((k:ℕ):ℂ)/((Real.pi:ℂ)^2*(((k:ℕ):ℂ)^2-((m:ℕ):ℂ)^2))) := by
    rw [hillFreeInteractionPerturbation,if_neg (not_or.mpr ⟨hjn,hjm⟩),← hki,hillFreeInteractionKernel_positive m k hkm]
  rw [hu]
  change (((Real.pi:ℂ)*((j:ℂ)+1))^2+((j:ℂ)+1)*d k-((Real.pi:ℂ)*(m:ℕ))^2)/
    ((Real.pi:ℂ)*((j:ℂ)+1))^2 =
    ((((Real.pi:ℂ)*((j:ℂ)+1))^2+((j:ℂ)+1)*(0:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/
      ((Real.pi:ℂ)*((j:ℂ)+1))^2)*
    (1+d k*(((k:ℕ):ℂ)/((Real.pi:ℂ)^2*(((k:ℕ):ℂ)^2-((m:ℕ):ℂ)^2))))
  simp only [mul_zero,add_zero]
  rw [← hk]
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsq := sub_ne_zero.mpr (pnat_complex_squares_ne hkm)
  field_simp [hpi,hsq]
  ring

def hillFreePeriodMultiplierApprox (n m : ℕ+) (N : ℕ) (d : lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  if m = n then 1 else hillPeriodEquationWeight n m*
    (-((Real.pi:ℂ)*(m:ℕ))/cos ((Real.pi:ℂ)*(m:ℕ)))*
      (hillEnergySequencePartialProduct n N ((((Real.pi:ℂ)*(m:ℕ))^2),hillZeroCoordinateShift m d 1)-
        hillEnergySequencePartialProduct n N ((((Real.pi:ℂ)*(m:ℕ))^2),d))

theorem tendsto_hillFreePeriodMultiplierApprox (n m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    Tendsto (fun N => hillFreePeriodMultiplierApprox n m N d) atTop (𝓝 (hillFreePeriodMultiplier n m d)) := by
  by_cases hmn : m = n
  · simp only [hillFreePeriodMultiplierApprox,hillFreePeriodMultiplier,if_pos hmn]
    exact tendsto_const_nhds
  · simp only [hillFreePeriodMultiplierApprox,hillFreePeriodMultiplier,if_neg hmn,
      hillEnergyProductCoordinateDerivative]
    exact ((tendsto_hillEnergySequencePartialProduct n _).sub
      (tendsto_hillEnergySequencePartialProduct n _)).const_mul _

theorem hillFreePeriodMultiplierApprox_factor (n m : ℕ+) (hmn : m ≠ n)
    (N : ℕ) (hN : (m:ℕ) ≤ N) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillFreePeriodMultiplierApprox n m N d = hillFreePeriodMultiplierApprox n m N 0*
      ∏ j ∈ ((Finset.range N).erase ((n:ℕ)-1)).erase ((m:ℕ)-1),
        (1+hillFreeInteractionPerturbation n m d j) := by
  simp only [hillFreePeriodMultiplierApprox,if_neg hmn]
  rw [hillEnergySequencePartialProduct_coordinate_difference n m hmn N hN,
    hillEnergySequencePartialProduct_coordinate_difference n m hmn N hN]
  have hprod : (∏ j ∈ ((Finset.range N).erase ((n:ℕ)-1)).erase ((m:ℕ)-1),
      hillEnergySequenceFactor ((((Real.pi:ℂ)*(m:ℕ))^2),d) j) =
      (∏ j ∈ ((Finset.range N).erase ((n:ℕ)-1)).erase ((m:ℕ)-1),
        hillEnergySequenceFactor ((((Real.pi:ℂ)*(m:ℕ))^2),0) j)*
      ∏ j ∈ ((Finset.range N).erase ((n:ℕ)-1)).erase ((m:ℕ)-1),
        (1+hillFreeInteractionPerturbation n m d j) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    exact hillEnergySequenceFactor_freeEnergy_interaction n m d j
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj)
  rw [hprod]
  ring

end NLS.KdV
