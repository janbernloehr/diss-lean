import NLS.KdV.HillProductCoordinateVariation
import NLS.ZakharovShabat.SourcePsiFree

/-! The literal free Hill product has its exact Euler normalization.
Its quadratic pullback divided by the actual free canonical root is
the rational kernel with poles at the two omitted free frequencies. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem singleSpectralPartialProduct_free_restore_Hill (n : ℕ+) (N : ℕ) (hN : (n:ℕ) ≤ N) (z : ℂ) :
    singleSpectralPartialProduct (fun k : ℤ => (Real.pi:ℂ)*k) z N =
      -2*z*(1-z^2/((Real.pi:ℂ)*(n:ℕ))^2)*hillEnergySequencePartialProduct n N (z^2,0) := by
  rw [singleSpectralPartialProduct_free_eq]
  let f : ℕ → ℂ := fun j => 1-z^2/((Real.pi:ℂ)*((j:ℂ)+1))^2
  have hmem : (n:ℕ)-1 ∈ Finset.range N := by simp only [Finset.mem_range]; have hn := n.pos; omega
  have hcast : (((n:ℕ)-1:ℕ):ℂ)+1 = ((n:ℕ):ℂ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using! congrArg (fun j : ℕ => (j:ℂ)) (Nat.sub_add_cancel n.property)
  have he : (∏ j ∈ (Finset.range N).erase ((n:ℕ)-1),f j) = hillEnergySequencePartialProduct n N (z^2,0) := by
    unfold hillEnergySequencePartialProduct
    apply Finset.prod_congr rfl
    intro j _
    change 1-z^2/((Real.pi:ℂ)*((j:ℂ)+1))^2 =
      (((Real.pi:ℂ)*((j:ℂ)+1))^2+((j:ℂ)+1)*0-z^2)/((Real.pi:ℂ)*((j:ℂ)+1))^2
    have hd := hillEnergyProduct_denominator_ne_zero j
    field_simp
    ring
  change -2*z*(∏ j ∈ Finset.range N,f j) = _
  rw [← Finset.mul_prod_erase (Finset.range N) f hmem,he]
  dsimp only [f]
  rw [hcast]
  ring

theorem hillEnergySequenceProduct_free_sine_identity (n : ℕ+) (z : ℂ) :
    z*(((Real.pi:ℂ)*(n:ℕ))^2-z^2)*hillEnergySequenceProduct n (z^2,0) =
      ((Real.pi:ℂ)*(n:ℕ))^2*sin z := by
  have hρ : Memℓp (fun k : ℤ => (Real.pi:ℂ)*k-(Real.pi:ℂ)*k) (2:ℝ≥0∞) := by
    simpa only [sub_self] using (zero_mem_ℓp' (E := fun _ : ℤ => ℂ) (p := (2:ℝ≥0∞)))
  have hs := (tendstoLocallyUniformlyOn_entireSingleSpectralProduct (by norm_num) _ hρ).tendsto_at (mem_univ z)
  rw [entireSingleSpectralProduct_free] at hs
  have hp := (tendsto_hillEnergySequencePartialProduct n (z^2,0)).const_mul
    (-2*z*(1-z^2/((Real.pi:ℂ)*(n:ℕ))^2))
  have he : ∀ᶠ N : ℕ in atTop,
      -2*z*(1-z^2/((Real.pi:ℂ)*(n:ℕ))^2)*hillEnergySequencePartialProduct n N (z^2,0) =
        singleSpectralPartialProduct (fun k : ℤ => (Real.pi:ℂ)*k) z N := by
    filter_upwards [eventually_ge_atTop (n:ℕ)] with N hN
    exact (singleSpectralPartialProduct_free_restore_Hill n N hN z).symm
  have h := tendsto_nhds_unique hs (hp.congr' he)
  have hd : ((Real.pi:ℂ)*(n:ℕ))^2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))
  field_simp [hd] at h
  linear_combination h

theorem hillFree_energy_denominator_ne_zero (n : ℕ+) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (0:CoeffPair 2)) :
    ((Real.pi:ℂ)*(n:ℕ))^2-z^2 ≠ 0 := by
  have hs : sin z ≠ 0 := by
    have hroot := sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) (0:CoeffPair 2) z hz
    rw [sourceCanonicalRoot_zero_source_eq_free_sine (by norm_num) (by norm_num) 0] at hroot
    exact fun h => hroot (by rw [h,mul_zero])
  intro he
  have h := hillEnergySequenceProduct_free_sine_identity n z
  rw [he,mul_zero,zero_mul] at h
  exact mul_ne_zero (pow_ne_zero 2 (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (by exact_mod_cast n.ne_zero))) hs h.symm

theorem hillEnergyProductPeriodIntegrand_free (n : ℕ+) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (0:CoeffPair 2)) :
    (2*z*hillEnergySequenceProduct n (z^2,0))/sourceCanonicalRoot (by norm_num) (by norm_num) (0:CoeffPair 2) z =
      I*((Real.pi:ℂ)*(n:ℕ))^2/(((Real.pi:ℂ)*(n:ℕ))^2-z^2) := by
  have hd := hillFree_energy_denominator_ne_zero n z hz
  have hroot := sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) (0:CoeffPair 2) z hz
  rw [sourceCanonicalRoot_zero_source_eq_free_sine (by norm_num) (by norm_num) 0] at hroot ⊢
  have h := hillEnergySequenceProduct_free_sine_identity n z
  apply (div_eq_div_iff hroot hd).mpr
  calc
    (2*z*hillEnergySequenceProduct n (z^2,0))*(((Real.pi:ℂ)*(n:ℕ))^2-z^2) =
        2*(z*(((Real.pi:ℂ)*(n:ℕ))^2-z^2)*hillEnergySequenceProduct n (z^2,0)) := by ring
    _ = 2*(((Real.pi:ℂ)*(n:ℕ))^2*sin z) := by rw [h]
    _ = (I*((Real.pi:ℂ)*(n:ℕ))^2)*(-2*I*sin z) := by
      linear_combination (2*((Real.pi:ℂ)*(n:ℕ))^2*sin z)*I_sq

end NLS.KdV
