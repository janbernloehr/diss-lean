import NLS.ZakharovShabat.EntireSpectralPairProducts
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Entire products with one spectral pair deleted

The omitted pair retains its constant normalization. The remaining finite
products converge locally uniformly everywhere, even at coincident endpoints.
Restoring the pair gives the full product with its normalization `-4`.
-/

noncomputable section
open Filter Topology Set
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- A symmetric cutoff omitting the nth pair and retaining its normalization. -/
def deletedSpectralPairPartialProduct (ξ η : ℤ → ℂ) (n : ℤ) (N : ℕ) (z : ℂ) : ℂ :=
  (∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n, spectralPairFactor ξ η z k) /
    spectralPairDenominator n

/-- The entire limit of the literal cutoffs with one pair deleted. -/
def deletedSpectralPairProduct (ξ η : ℤ → ℂ) (n : ℤ) : ℂ → ℂ :=
  NLS.ComplexAnalysis.entireSequenceLimit (deletedSpectralPairPartialProduct ξ η n)

/-- Restoring a deleted pair requires no division by a spectral variable. -/
theorem spectralPairPartialProduct_eq_deleted (ξ η : ℤ → ℂ) (n : ℤ) (N : ℕ)
    (hn : n.natAbs ≤ N) (z : ℂ) :
    spectralPairPartialProduct ξ η z N =
      (-4*(ξ n-z)*(η n-z))*deletedSpectralPairPartialProduct ξ η n N z := by
  have hm : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    simp only [Finset.mem_Icc]; constructor <;> omega
  rw [spectralPairPartialProduct, ← Finset.mul_prod_erase _ _ hm, spectralPairFactor_eq_div,
    deletedSpectralPairPartialProduct]
  ring

/-- Every cutoff after deletion is still an entire polynomial. -/
theorem analyticOnNhd_deletedSpectralPairPartialProduct (ξ η : ℤ → ℂ) (n : ℤ) (N : ℕ) :
    AnalyticOnNhd ℂ (deletedSpectralPairPartialProduct ξ η n N) univ := by
  intro z _
  unfold deletedSpectralPairPartialProduct
  exact (Finset.analyticAt_fun_prod _ (fun k _ =>
    analyticOnNhd_spectralPairFactor ξ η k univ z (mem_univ _))).div
      analyticAt_const (spectralPairDenominator_ne_zero n)

/-- Changing only the removed endpoints leaves every deleted cutoff unchanged. -/
theorem deletedSpectralPairPartialProduct_congr_away (ξ η α β : ℤ → ℂ) (n : ℤ)
    (hξ : ∀ k, k ≠ n → ξ k = α k) (hη : ∀ k, k ≠ n → η k = β k) :
    deletedSpectralPairPartialProduct ξ η n = deletedSpectralPairPartialProduct α β n := by
  funext N z
  unfold deletedSpectralPairPartialProduct
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hkn := (Finset.mem_erase.mp hk).1
  rw [spectralPairFactor_eq_div,spectralPairFactor_eq_div,hξ k hkn,hη k hkn]

/-- The remaining entire product is independent of the values of the removed pair. -/
theorem deletedSpectralPairProduct_congr_away (ξ η α β : ℤ → ℂ) (n : ℤ)
    (hξ : ∀ k, k ≠ n → ξ k = α k) (hη : ∀ k, k ≠ n → η k = β k) :
    deletedSpectralPairProduct ξ η n = deletedSpectralPairProduct α β n := by
  unfold deletedSpectralPairProduct
  rw [deletedSpectralPairPartialProduct_congr_away ξ η α β n hξ hη]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Away from the selected endpoints, the deleted cutoffs converge to the literal quotient. -/
theorem tendstoLocallyUniformlyOn_deletedSpectralPairPartialProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun k => ξ k-(Real.pi : ℂ)*k) p)
    (hη : Memℓp (fun k => η k-(Real.pi : ℂ)*k) p) (n : ℤ) :
    TendstoLocallyUniformlyOn (deletedSpectralPairPartialProduct ξ η n)
      (fun z => entireSpectralPairProduct ξ η z/(-4*(ξ n-z)*(η n-z))) atTop {ξ n,η n}ᶜ := by
  have hc : TendstoLocallyUniformlyOn (fun _ : ℕ => fun z : ℂ => -4*(ξ n-z)*(η n-z))
      (fun z => -4*(ξ n-z)*(η n-z)) atTop {ξ n,η n}ᶜ := by
    intro v hv z _
    exact ⟨univ,Filter.univ_mem,Filter.Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hv)⟩
  have h := ((tendstoLocallyUniformlyOn_entireSpectralPairProduct hp ξ η hξ hη).mono
    (subset_univ _)).div₀ hc
    ((analyticOnNhd_entireSpectralPairProduct hp ξ η hξ hη).continuousOn.mono (subset_univ _))
    (by fun_prop) (by
      intro z hz
      have hz' : z ≠ ξ n ∧ z ≠ η n := by simpa using hz
      exact mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hz'.1.symm))
        (sub_ne_zero.mpr hz'.2.symm))
  apply h.congr_inseparable
  filter_upwards [eventually_ge_atTop n.natAbs] with N hN
  intro z hz
  apply Inseparable.of_eq
  have hz' : z ≠ ξ n ∧ z ≠ η n := by simpa using hz
  have hd : -4*(ξ n-z)*(η n-z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hz'.1.symm))
      (sub_ne_zero.mpr hz'.2.symm)
  change spectralPairPartialProduct ξ η z N/(-4*(ξ n-z)*(η n-z)) = _
  rw [spectralPairPartialProduct_eq_deleted ξ η n N hN z, mul_div_cancel_left₀ _ hd]

/-- Deleting a pair preserves locally uniform convergence on the whole complex plane. -/
theorem tendstoLocallyUniformlyOn_deletedSpectralPairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun k => ξ k-(Real.pi : ℂ)*k) p)
    (hη : Memℓp (fun k => η k-(Real.pi : ℂ)*k) p) (n : ℤ) :
    TendstoLocallyUniformlyOn (deletedSpectralPairPartialProduct ξ η n)
      (deletedSpectralPairProduct ξ η n) atTop univ :=
  NLS.ComplexAnalysis.tendstoLocallyUniformlyOn_entireSequenceLimit _
    (fun N => differentiableOn_univ.mp
      (analyticOnNhd_deletedSpectralPairPartialProduct ξ η n N).differentiableOn)
    {ξ n,η n} (Set.to_countable _) _
    (tendstoLocallyUniformlyOn_deletedSpectralPairPartialProduct hp ξ η hξ hη n)

/-- The deleted-pair product is entire, including at both removed roots. -/
theorem analyticOnNhd_deletedSpectralPairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun k => ξ k-(Real.pi : ℂ)*k) p)
    (hη : Memℓp (fun k => η k-(Real.pi : ℂ)*k) p) (n : ℤ) :
    AnalyticOnNhd ℂ (deletedSpectralPairProduct ξ η n) univ :=
  ((tendstoLocallyUniformlyOn_deletedSpectralPairProduct hp ξ η hξ hη n).differentiableOn
    (Filter.Eventually.of_forall (fun N =>
      (analyticOnNhd_deletedSpectralPairPartialProduct ξ η n N).differentiableOn))
    isOpen_univ).analyticOnNhd isOpen_univ

/-- Derivatives of the deleted cutoffs converge locally uniformly, including at the removed roots. -/
theorem tendstoLocallyUniformlyOn_deriv_deletedSpectralPairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun k => ξ k-(Real.pi : ℂ)*k) p)
    (hη : Memℓp (fun k => η k-(Real.pi : ℂ)*k) p) (n : ℤ) :
    TendstoLocallyUniformlyOn (fun N => deriv (deletedSpectralPairPartialProduct ξ η n N))
      (deriv (deletedSpectralPairProduct ξ η n)) atTop univ :=
  (tendstoLocallyUniformlyOn_deletedSpectralPairProduct hp ξ η hξ hη n).deriv
    (Filter.Eventually.of_forall (fun N =>
      (analyticOnNhd_deletedSpectralPairPartialProduct ξ η n N).differentiableOn)) isOpen_univ

/-- The entire product factorization holds also at collisions and zeros. -/
theorem entireSpectralPairProduct_eq_deleted (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun k => ξ k-(Real.pi : ℂ)*k) p)
    (hη : Memℓp (fun k => η k-(Real.pi : ℂ)*k) p) (n : ℤ) (z : ℂ) :
    entireSpectralPairProduct ξ η z =
      (-4*(ξ n-z)*(η n-z))*deletedSpectralPairProduct ξ η n z := by
  have ht := ((tendstoLocallyUniformlyOn_deletedSpectralPairProduct hp ξ η hξ hη n).tendsto_at
    (mem_univ z)).const_mul (-4*(ξ n-z)*(η n-z))
  have he : ∀ᶠ N : ℕ in atTop, (-4*(ξ n-z)*(η n-z))*deletedSpectralPairPartialProduct ξ η n N z =
      spectralPairPartialProduct ξ η z N := by
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    exact (spectralPairPartialProduct_eq_deleted ξ η n N hN z).symm
  exact tendsto_nhds_unique
    ((tendstoLocallyUniformlyOn_entireSpectralPairProduct hp ξ η hξ hη).tendsto_at (mem_univ z))
    (ht.congr' he)

end NLS.ZakharovShabat
