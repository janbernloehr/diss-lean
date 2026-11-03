import NLS.KdV.HillEnergySequenceProduct
import NLS.ComplexAnalysis.SingleFactorVariation

/-! Exact literal Hill cutoff variations in one inverse-index l2
coordinate. A coordinate displacement by z moves its energy zero by m*z. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillZeroCoordinateShift (m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) : lp (fun _ : ℕ+ => ℂ) 2 :=
  d+z • lp.single 2 m 1

theorem positive_cutoff_index_eq (m : ℕ+) (j : ℕ) :
    (⟨j+1,by omega⟩ : ℕ+) = m ↔ j = (m:ℕ)-1 := by
  constructor
  · intro h
    have h' := congrArg (fun r : ℕ+ => (r:ℕ)) h
    change j+1 = (m:ℕ) at h'
    omega
  · intro h
    apply Subtype.ext
    change j+1 = (m:ℕ)
    have hm := m.pos
    omega

theorem hillZeroCoordinateShift_apply (m k : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    hillZeroCoordinateShift m d z k = d k+if k = m then z else 0 := by
  simp only [hillZeroCoordinateShift,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,
    smul_eq_mul,lp.single_apply,Pi.single_apply]
  by_cases h : k = m
  · simp only [h,ite_true,mul_one]
  · simp only [if_neg h,mul_zero]

theorem hillEnergySequenceFactor_shift_other (m : ℕ+) (E : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (z : ℂ) (j : ℕ) (hj : j ≠ (m:ℕ)-1) :
    hillEnergySequenceFactor (E,hillZeroCoordinateShift m d z) j = hillEnergySequenceFactor (E,d) j := by
  unfold hillEnergySequenceFactor
  dsimp only
  apply congrArg (fun a : ℂ => (((Real.pi:ℂ)*((j:ℂ)+1))^2+((j:ℂ)+1)*a-E)/((Real.pi:ℂ)*((j:ℂ)+1))^2)
  let k : ℕ+ := ⟨j+1,by omega⟩
  change hillZeroCoordinateShift m d z k = d k
  have hk : k ≠ m := fun h => hj ((positive_cutoff_index_eq m j).mp h)
  have hv := hillZeroCoordinateShift_apply m k d z
  rw [if_neg hk,add_zero] at hv
  exact hv

theorem hillEnergySequenceFactor_shift_selected (m : ℕ+) (E : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    hillEnergySequenceFactor (E,hillZeroCoordinateShift m d z) ((m:ℕ)-1) =
      hillEnergySequenceFactor (E,d) ((m:ℕ)-1)+z*((m:ℕ)/((Real.pi:ℂ)*(m:ℕ))^2) := by
  have hm : (m:ℕ)-1+1 = (m:ℕ) := Nat.sub_add_cancel m.property
  have hindex : (⟨(m:ℕ)-1+1,by omega⟩ : ℕ+) = m := (positive_cutoff_index_eq m _).mpr rfl
  have hcast : (((m:ℕ)-1:ℕ):ℂ)+1 = ((m:ℕ):ℂ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun r : ℕ => (r:ℂ)) hm
  unfold hillEnergySequenceFactor
  dsimp only
  rw [hindex,hcast,hillZeroCoordinateShift_apply,if_pos rfl]
  ring

theorem hillEnergySequencePartialProduct_coordinate_affine (n m : ℕ+) (N : ℕ) (E : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    hillEnergySequencePartialProduct n N (E,hillZeroCoordinateShift m d z) =
      hillEnergySequencePartialProduct n N (E,d)+z*(
        hillEnergySequencePartialProduct n N (E,hillZeroCoordinateShift m d 1)-
          hillEnergySequencePartialProduct n N (E,d)) := by
  have h0 : hillZeroCoordinateShift m d 0 = d := by simp [hillZeroCoordinateShift]
  have h := finite_product_single_factor_affine ((Finset.range N).erase ((n:ℕ)-1)) ((m:ℕ)-1)
    (fun w j => hillEnergySequenceFactor (E,hillZeroCoordinateShift m d w) j)
    (fun w j hj => by rw [hillEnergySequenceFactor_shift_other m E d w j hj,h0])
    (fun w => by simp only [h0,hillEnergySequenceFactor_shift_selected]; ring) z
  simpa only [h0,hillEnergySequencePartialProduct] using h

def hillEnergySequenceZero (m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  ((Real.pi:ℂ)*(m:ℕ))^2+(m:ℕ)*d m

theorem hillEnergySequenceFactor_selected_eq (m : ℕ+) (E : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergySequenceFactor (E,d) ((m:ℕ)-1) =
      (hillEnergySequenceZero m d-E)/((Real.pi:ℂ)*(m:ℕ))^2 := by
  have hm : (m:ℕ)-1+1 = (m:ℕ) := Nat.sub_add_cancel m.property
  have hindex := (positive_cutoff_index_eq m ((m:ℕ)-1)).mpr rfl
  have hcast : (((m:ℕ)-1:ℕ):ℂ)+1 = ((m:ℕ):ℂ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun r : ℕ => (r:ℂ)) hm
  simp only [hillEnergySequenceFactor,hindex,hcast,hillEnergySequenceZero]

theorem hillEnergySequencePartialProduct_coordinate_restore (n m : ℕ+) (hmn : m ≠ n)
    (N : ℕ) (hN : (m:ℕ) ≤ N) (E : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    (hillEnergySequenceZero m d-E)*(
      hillEnergySequencePartialProduct n N (E,hillZeroCoordinateShift m d 1)-
        hillEnergySequencePartialProduct n N (E,d)) = (m:ℕ)*hillEnergySequencePartialProduct n N (E,d) := by
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
  have h0 : hillZeroCoordinateShift m d 0 = d := by simp [hillZeroCoordinateShift]
  have h := finite_product_single_factor_restore ((Finset.range N).erase ((n:ℕ)-1)) ((m:ℕ)-1)
    (fun w j => hillEnergySequenceFactor (E,hillZeroCoordinateShift m d w) j) hmem
    (fun w j hj => by rw [hillEnergySequenceFactor_shift_other m E d w j hj,h0])
  simp only [h0] at h
  change hillEnergySequenceFactor (E,d) ((m:ℕ)-1)*
    (hillEnergySequencePartialProduct n N (E,hillZeroCoordinateShift m d 1)-
      hillEnergySequencePartialProduct n N (E,d)) =
    (hillEnergySequenceFactor (E,hillZeroCoordinateShift m d 1) ((m:ℕ)-1)-
      hillEnergySequenceFactor (E,d) ((m:ℕ)-1))*hillEnergySequencePartialProduct n N (E,d) at h
  rw [hillEnergySequenceFactor_shift_selected] at h
  simp only [one_mul,add_sub_cancel_left] at h
  rw [hillEnergySequenceFactor_selected_eq] at h
  have hd : ((Real.pi:ℂ)*(m:ℕ))^2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast m.ne_zero))
  field_simp [hd] at h
  exact h

theorem hillEnergySequencePartialProduct_omitted_shift (n : ℕ+) (N : ℕ) (E : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    hillEnergySequencePartialProduct n N (E,hillZeroCoordinateShift n d z) =
      hillEnergySequencePartialProduct n N (E,d) := by
  unfold hillEnergySequencePartialProduct
  exact Finset.prod_congr rfl (fun j hj =>
    hillEnergySequenceFactor_shift_other n E d z j (Finset.ne_of_mem_erase hj))

end NLS.KdV
