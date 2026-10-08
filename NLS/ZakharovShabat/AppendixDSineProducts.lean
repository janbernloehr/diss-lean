import NLS.ZakharovShabat.SingleSpectralProductEndpoints
import NLS.ZakharovShabat.SourceDeletedFreeSine
import NLS.ZakharovShabat.SourcePsiDeletedProductNonzero

/-! # The literal sine-product normalization in Appendix D

The earlier single-root product is normalized to the free discriminant
 derivative -2 sin(z). Appendix D instead uses minus the root product.
The deleted product also restores its omitted normalization denominator.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full entire product with the prefactor printed in D.5. -/
def appendixDProduct (t : ℂ × Coeff p) : ℂ := -(1/2:ℂ)*jointSingleSpectralProduct t

/-- The entire product omitting index n, with the prefactor printed in D.4. -/
def appendixDDeletedProduct (n : ℤ) (t : ℂ × Coeff p) : ℂ :=
  -singleSpectralDenominator n*jointDeletedSingleSpectralProduct n t

/-- Full literal symmetric cutoffs converge with exactly the source normalization. -/
theorem tendsto_appendixDProduct (hp : p ≠ ⊤) (t : ℂ × Coeff p) :
    Tendsto (fun N : ℕ => -∏ m ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
      (displacedRoots t.2 m-t.1)/singleSpectralDenominator m) atTop (𝓝 (appendixDProduct t)) := by
  have h := ((tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp
    (displacedRoots t.2) (memℓp_displacedRoots t.2)).tendsto_at (mem_univ t.1)).const_mul (-(1/2:ℂ))
  simpa [appendixDProduct, jointSingleSpectralProduct, singleSpectralPartialProduct,
    singleSpectralFactor, mul_assoc] using h

/-- Deleted literal symmetric cutoffs converge, including at the omitted root. -/
theorem tendsto_appendixDDeletedProduct (hp : p ≠ ⊤) (n : ℤ) (t : ℂ × Coeff p) :
    Tendsto (fun N : ℕ => -∏ m ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase n,
      (displacedRoots t.2 m-t.1)/singleSpectralDenominator m) atTop
      (𝓝 (appendixDDeletedProduct n t)) := by
  have h := ((tendstoUniformlyOn_jointDeletedSingleSpectralProduct_finite hp n
    {t.1} isCompact_singleton {t.2} ‖t.2‖ (norm_nonneg _)
    (by rintro a (rfl : a = t.2); exact le_rfl)).tendsto_at
      (show t ∈ ({t.1} : Set ℂ) ×ˢ {t.2} from ⟨rfl,rfl⟩)).const_mul
      (-singleSpectralDenominator n)
  have he (N : ℕ) : -singleSpectralDenominator n *
      jointDeletedSingleSpectralPartialProduct n N t =
      -(∏ m ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase n,
        (displacedRoots t.2 m-t.1)/singleSpectralDenominator m) := by
    unfold jointDeletedSingleSpectralPartialProduct singleSpectralFactor
    field_simp
  simpa only [he, appendixDDeletedProduct] using h

/-- D.5's product is jointly entire throughout every finite Banach exponent. -/
theorem analyticOnNhd_appendixDProduct (hp : p ≠ ⊤) :
    AnalyticOnNhd ℂ (appendixDProduct (p := p)) univ :=
  analyticOnNhd_const.mul (analyticOnNhd_jointSingleSpectralProduct_finite hp)

/-- D.4's deleted product is jointly entire, including p=1. -/
theorem analyticOnNhd_appendixDDeletedProduct (hp : p ≠ ⊤) (n : ℤ) :
    AnalyticOnNhd ℂ (appendixDDeletedProduct (p := p) n) univ :=
  analyticOnNhd_const.mul (analyticOnNhd_jointDeletedSingleSpectralProduct_finite hp n)

omit [Fact (1 ≤ p)] in
/-- The normalized full product has the printed free value sin(z). -/
theorem appendixDProduct_zero (z : ℂ) : appendixDProduct (z,(0:Coeff p)) = Complex.sin z := by
  have he : displacedRoots (0:Coeff p) = fun n : ℤ => (Real.pi:ℂ)*n := by
    funext n
    simp [displacedRoots]
  rw [appendixDProduct, jointSingleSpectralProduct, he, entireSingleSpectralProduct_free]
  ring

/-- Restoring the omitted source factor recovers the full product. -/
theorem appendixDProduct_eq_deleted (hp : p ≠ ⊤) (n : ℤ) (t : ℂ × Coeff p) :
    appendixDProduct t = ((displacedRoots t.2 n-t.1)/singleSpectralDenominator n)*
      appendixDDeletedProduct n t := by
  rw [appendixDProduct, jointSingleSpectralProduct_eq_deleted_finite hp n t,
    appendixDDeletedProduct]
  field_simp

/-- At zero displacement the deleted source product has its literal denominator factor. -/
theorem appendixDDeletedProduct_zero (hp : p ≠ ⊤) (n : ℤ) (z : ℂ) :
    appendixDDeletedProduct n (z,(0:Coeff p)) = -singleSpectralDenominator n*freeSineQuotient n z := by
  let q : ℝ≥0∞ := max p 2
  have hq1 : 1 < q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  have hq : q ≠ ⊤ := (max_lt hp.lt_top (by norm_num)).ne
  have h := congrFun (jointDeletedSingleSpectralProduct_zero_eq_freeSineQuotient
    (p := q) hq hq1 n) z
  have hz : singleProductExponentMap (le_max_left p 2) (z,(0:Coeff p)) = (z,(0:Coeff q)) := by
    ext <;> simp [singleProductExponentMap]
  rw [← hz, jointDeletedSingleSpectralProduct_exponentMap] at h
  exact congrArg (fun w : ℂ => -singleSpectralDenominator n*w) h

/-- The full product has exactly the prescribed roots, including free centers. -/
theorem appendixDProduct_eq_zero_iff (hp : p ≠ ⊤) (a : Coeff p) (z : ℂ) :
    appendixDProduct (z,a) = 0 ↔ ∃ k : ℤ, displacedRoots a k = z := by
  rw [appendixDProduct, mul_eq_zero]
  simpa using jointSingleSpectralProduct_eq_zero_iff_of_lp hp a z

/-- Every retained root is a zero of the source's deleted product. -/
theorem appendixDDeletedProduct_root (hp : p ≠ ⊤) (n k : ℤ) (hnk : k ≠ n)
    (a : Coeff p) : appendixDDeletedProduct n (displacedRoots a k,a) = 0 := by
  classical
  have hlim := tendsto_appendixDDeletedProduct hp n (displacedRoots a k,a)
  have hevent : ∀ᶠ N : ℕ in atTop,
      -(∏ m ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase n,
        (displacedRoots a m-displacedRoots a k)/singleSpectralDenominator m) = (0:ℂ) := by
    filter_upwards [eventually_ge_atTop k.natAbs] with N hN
    have hk : k ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase n := by
      simp only [Finset.mem_erase, Finset.mem_Icc]
      exact ⟨hnk, by omega, by omega⟩
    rw [Finset.prod_eq_zero hk (by simp), neg_zero]
  exact tendsto_nhds_unique (hlim.congr' hevent) tendsto_const_nhds

/-- No retained root means the source's deleted product is nonzero, also at p=1. -/
theorem appendixDDeletedProduct_ne_zero_of_off_other (hp : p ≠ ⊤) (n : ℤ)
    (z : ℂ) (a : Coeff p) (hother : ∀ k : ℤ, k ≠ n → z ≠ displacedRoots a k) :
    appendixDDeletedProduct n (z,a) ≠ 0 := by
  let q : ℝ≥0∞ := max p 2
  have hq1 : 1 < q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  have hq : q ≠ ⊤ := (max_lt hp.lt_top (by norm_num)).ne
  have h := jointDeletedSingleSpectralProduct_ne_zero_of_off_other hq hq1 n z
    (Coeff.exponentInclusion (le_max_left p 2) a) (by
      intro k hk
      simpa only [displacedRoots_exponentInclusion] using hother k hk)
  have ht : (z,Coeff.exponentInclusion (le_max_left p 2) a) =
      singleProductExponentMap (le_max_left p 2) (z,a) := rfl
  rw [ht, jointDeletedSingleSpectralProduct_exponentMap] at h
  exact mul_ne_zero (neg_ne_zero.mpr (singleSpectralDenominator_ne_zero n)) h

/-- The deleted product has exactly the retained roots, with no simplicity assumption. -/
theorem appendixDDeletedProduct_eq_zero_iff (hp : p ≠ ⊤) (n : ℤ) (a : Coeff p) (z : ℂ) :
    appendixDDeletedProduct n (z,a) = 0 ↔ ∃ k : ℤ, k ≠ n ∧ displacedRoots a k = z := by
  constructor
  · intro hz
    by_contra h
    push Not at h
    exact appendixDDeletedProduct_ne_zero_of_off_other hp n z a
      (fun k hk => Ne.symm (h k hk)) hz
  · rintro ⟨k,hkn,rfl⟩
    exact appendixDDeletedProduct_root hp n k hkn a

/-- Along any escaping path outside fixed free discs, the normalized source product
has the sine asymptotic. Local uniformity in the displacement is a separate assertion. -/
theorem tendsto_appendixDProduct_div_sin_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (a : Coeff p) (z : α → ℂ)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi:ℂ)*n‖) :
    Tendsto (fun i => appendixDProduct (z i,a)/Complex.sin (z i)) l (𝓝 1) := by
  have he (w : ℂ) : appendixDProduct (w,a)/Complex.sin w =
      entireSingleSpectralProduct (displacedRoots a) w/(-2*Complex.sin w) := by
    simp only [appendixDProduct, jointSingleSpectralProduct, div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [he]
  exact tendsto_entireSingleSpectralProduct_div_free_of_separated hp
    (displacedRoots a) (memℓp_displacedRoots a) z hescape hr hrπ hsep

end NLS.ZakharovShabat
