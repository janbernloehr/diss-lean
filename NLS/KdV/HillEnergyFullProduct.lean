import NLS.KdV.HillIndependentProductRestoration
import NLS.KdV.HillProductDirectionalDerivative

/-! The literal full positive Hill energy product, jointly entire in
energy and inverse-index l2 data, with exact restoration of ANY omitted
factor and the original balanced full frequency product normalization. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillEnergySequenceFullPartialProduct (N : ℕ) (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  ∏ j ∈ Finset.range N,hillEnergySequenceFactor t j

def hillEnergySequenceFullProduct (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  jointDeletedSingleSpectralProduct (p := 2) 0 (0,hillEnergyRawProductEmbedding t)

theorem analyticAt_hillEnergySequenceFullProduct (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    AnalyticAt ℂ hillEnergySequenceFullProduct t :=
  (analyticOnNhd_jointDeletedSingleSpectralProduct (by norm_num) (by norm_num) 0 _ (mem_univ _)).comp
    (f := fun s : ℂ × lp (fun _ : ℕ+ => ℂ) 2 => (0,hillEnergyRawProductEmbedding s))
    (analyticAt_const.prod (analyticAt_hillEnergyRawProductEmbedding t))

theorem hillEnergySequenceFullPartialProduct_eq_embedding (N : ℕ) (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergySequenceFullPartialProduct N t =
      jointDeletedSingleSpectralPartialProduct 0 N (0,hillEnergyRawProductEmbedding t) := by
  rw [centered_deleted_single_partialProduct _ (hillEnergyRawProductEmbedding_nonpos t)]
  apply Finset.prod_congr rfl
  intro j _
  let m : ℕ+ := ⟨j+1,by omega⟩
  have he : (j:ℤ)+1 = ((m:ℕ):ℤ) := by
    change (j:ℤ)+1 = ((j+1:ℕ):ℤ)
    simp only [Nat.cast_add,Nat.cast_one]
  have hc : ((m:ℕ):ℂ) = (j:ℂ)+1 := by
    change ((j+1:ℕ):ℂ) = (j:ℂ)+1
    simp only [Nat.cast_add,Nat.cast_one]
  rw [he,hillEnergyRawProductEmbedding_positive,hc]
  unfold hillEnergySequenceFactor
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hj : (j:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero j
  field_simp [hp,hj]
  ring

theorem tendsto_hillEnergySequenceFullPartialProduct (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    Tendsto (fun N => hillEnergySequenceFullPartialProduct N t) atTop (𝓝 (hillEnergySequenceFullProduct t)) := by
  simp_rw [hillEnergySequenceFullPartialProduct_eq_embedding]
  exact tendsto_jointDeletedSingleSpectralPartialProduct (by norm_num) (by norm_num) 0 _

theorem hillEnergySequenceFullPartialProduct_restore (n : ℕ+) (N : ℕ) (hN : (n:ℕ) ≤ N)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergySequenceFullPartialProduct N t =
      ((hillEnergySequenceZero n t.2-t.1)/((Real.pi:ℂ)*(n:ℕ))^2)*hillEnergySequencePartialProduct n N t := by
  have hmem : (n:ℕ)-1 ∈ Finset.range N := by simp only [Finset.mem_range]; have := n.pos; omega
  have h := Finset.mul_prod_erase (Finset.range N) (hillEnergySequenceFactor t) hmem
  rw [hillEnergySequenceFactor_selected_eq] at h
  exact h.symm

theorem hillEnergySequenceFullProduct_restore (n : ℕ+) (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergySequenceFullProduct t =
      ((hillEnergySequenceZero n t.2-t.1)/((Real.pi:ℂ)*(n:ℕ))^2)*hillEnergySequenceProduct n t := by
  have hfull := tendsto_hillEnergySequenceFullPartialProduct t
  have hdel := (tendsto_hillEnergySequencePartialProduct n t).const_mul
    ((hillEnergySequenceZero n t.2-t.1)/((Real.pi:ℂ)*(n:ℕ))^2)
  apply tendsto_nhds_unique hfull
  apply hdel.congr'
  filter_upwards [eventually_ge_atTop (n:ℕ)] with N hN
  exact (hillEnergySequenceFullPartialProduct_restore n N hN t).symm

theorem jointSingleSpectralProduct_eq_full_Hill_product (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    jointSingleSpectralProduct (z,hillIndependentFrequencyDisplacement (c,d)) =
      -2*z*hillEnergySequenceFullProduct (z^2-c,d) := by
  rw [hillEnergySequenceFullProduct_restore (1:ℕ+)]
  have h := jointSingleSpectralProduct_independent_Hill_restore (1:ℕ+) c d z
  convert h using 1
  ring

theorem hillEnergySequenceFullProduct_at_root (m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergySequenceFullProduct (hillEnergySequenceZero m d,d) = 0 := by
  rw [hillEnergySequenceFullProduct_restore m,sub_self,zero_div,zero_mul]


theorem hillEnergySequenceFullProduct_coordinate_affine (m : ℕ+) (E : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (w : ℂ) :
    hillEnergySequenceFullProduct (E,hillZeroCoordinateShift m d w) = hillEnergySequenceFullProduct (E,d)+
      w*(hillEnergySequenceFullProduct (E,hillZeroCoordinateShift m d 1)-hillEnergySequenceFullProduct (E,d)) := by
  rw [hillEnergySequenceFullProduct_restore m (E,hillZeroCoordinateShift m d w),
    hillEnergySequenceFullProduct_restore m (E,d),
    hillEnergySequenceFullProduct_restore m (E,hillZeroCoordinateShift m d 1)]
  rw [hillEnergySequenceZero_shift_selected,hillEnergySequenceZero_shift_selected,
    hillEnergySequenceProduct_omitted_shift,hillEnergySequenceProduct_omitted_shift]
  ring

end NLS.KdV
