import NLS.ZakharovShabat.FreeSpectralProducts
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Analysis.PSeries

/-!
# Locally uniform free Euler products

The quadratic Euler factors admit a summable bound on every compact set.
The resulting locally uniform limit is identified by the already proved
pointwise free product formula, including at every free eigenvalue.
-/

noncomputable section
open Filter Topology
namespace NLS.ZakharovShabat

/-- The Euler factors converge locally uniformly on the whole complex plane. -/
theorem hasProdLocallyUniformlyOn_eulerFactors :
    HasProdLocallyUniformlyOn (fun j : ℕ => fun z : ℂ => 1-z^2/((j : ℂ)+1)^2)
      (fun z => ∏' j : ℕ, (1-z^2/((j : ℂ)+1)^2)) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R,hR,hb⟩ := hK.isBounded.exists_pos_norm_le
  have hs : Summable (fun j : ℕ => 1/((j : ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hprod := (hs.mul_left (R^2)).hasProdUniformlyOn_one_add
    (f := fun j : ℕ => fun z : ℂ => -(z^2/((j : ℂ)+1)^2)) hK
    (Filter.Eventually.of_forall (fun j z hz => by
      simp only [norm_neg, norm_div, norm_pow]
      have hn : ‖(j : ℂ)+1‖ = (j : ℝ)+1 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_of_nonneg]
        positivity
      rw [hn, mul_one_div]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) (hb z hz) 2) (by positivity)))
    (fun j => by fun_prop)
  simpa only [← sub_eq_add_neg] using hprod

/-- The unordered Euler product is continuous at every complex parameter. -/
theorem continuous_eulerProduct : Continuous (fun z : ℂ => ∏' j : ℕ, (1-z^2/((j : ℂ)+1)^2)) := by
  apply continuousOn_univ.mp
  exact hasProdLocallyUniformlyOn_eulerFactors.continuousOn
    (Filter.Eventually.of_forall (fun s => by fun_prop)).frequently

/-- Symmetric free products converge locally uniformly at every complex parameter, including lattice values. -/
theorem tendstoLocallyUniformlyOn_freeSpectralPartialProduct (h : ℂ) (hh : h ≠ 0) :
    TendstoLocallyUniformlyOn (fun N z => freeSpectralPartialProduct h z N)
      (fun z => (h/(Real.pi : ℂ)*Complex.sin ((Real.pi : ℂ)*z/h))^2) atTop Set.univ := by
  have he := (hasProdLocallyUniformlyOn_eulerFactors.comp (t := Set.univ) (fun z : ℂ => z/h)
    (fun _ _ => Set.mem_univ _) (by fun_prop)).tendstoLocallyUniformlyOn_finsetRange
  have hc : ContinuousOn (fun z : ℂ => ∏' j : ℕ, (1-(z/h)^2/((j : ℂ)+1)^2)) Set.univ :=
    (continuous_eulerProduct.comp (by fun_prop)).continuousOn
  have hz : TendstoLocallyUniformlyOn (fun _ : ℕ => fun z : ℂ => z) (fun z => z) atTop Set.univ := by
    intro v hv z _
    exact ⟨Set.univ,Filter.univ_mem,Filter.Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hv)⟩
  have hm := hz.mul₀ he continuousOn_id hc
  have hmc := continuousOn_id.mul hc
  have hs := hm.mul₀ hm hmc hmc
  have hp : TendstoLocallyUniformlyOn (fun N z => freeSpectralPartialProduct h z N)
      (fun z => (z*(∏' j : ℕ, (1-(z/h)^2/((j : ℂ)+1)^2)))^2) atTop Set.univ := by
    apply (hs.congr ?_).congr_right (fun _ _ => (pow_two _).symm)
    intro N z _
    simp only [Pi.mul_apply, freeSpectralPartialProduct_eq h z hh, ← pow_two]
    congr 2
    apply Finset.prod_congr rfl
    intro j _
    rw [div_pow, mul_pow, div_div]
  exact hp.congr_right (fun z _ => tendsto_nhds_unique (hp.tendsto_at (Set.mem_univ z))
    (tendsto_freeSpectralPartialProduct h z hh))

end NLS.ZakharovShabat
