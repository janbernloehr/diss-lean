import NLS.ComplexAnalysis.FinitePowerSeriesJets

/-!
# Scalar Taylor nullity is the truncated vanishing order

If a nonzero scalar series has order `m`, multiplication modulo degree `N`
has kernel dimension `min N m`. The kernel is exactly the set of vectors
whose first `N-m` coefficients vanish; no convergence hypothesis is needed.
-/

noncomputable section
open Complex PowerSeries
namespace NLS.ComplexAnalysis

/-- Restrict a finite coefficient vector to an initial segment. -/
def finiteJetPrefix (N K : ℕ) (hKN : K ≤ N) : (Fin N → ℂ) →ₗ[ℂ] (Fin K → ℂ) where
  toFun v j := v ⟨j.val,j.isLt.trans_le hKN⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Restricting a zero-extended formal series recovers its finite prefix. -/
theorem seriesFiniteJet_finiteJetSeries_prefix (N K : ℕ) (hKN : K ≤ N) (v : Fin N → ℂ) :
    seriesFiniteJet K (finiteJetSeries N v) = finiteJetPrefix N K hKN v := by
  funext j
  simp only [seriesFiniteJet_apply,coeff_finiteJetSeries,dif_pos (j.isLt.trans_le hKN)]
  rfl

/-- Every finite prefix has an extension to the longer coefficient vector. -/
theorem finiteJetPrefix_surjective (N K : ℕ) (hKN : K ≤ N) :
    Function.Surjective (finiteJetPrefix N K hKN) := by
  intro v
  refine ⟨fun j => if h : j.val < K then v ⟨j.val,h⟩ else 0,?_⟩
  funext j
  simp [finiteJetPrefix,j.isLt]

/-- The kernel of prefix restriction consists of the freely chosen remaining coordinates. -/
theorem finrank_ker_finiteJetPrefix (N K : ℕ) (hKN : K ≤ N) :
    Module.finrank ℂ (LinearMap.ker (finiteJetPrefix N K hKN)) = N-K := by
  have h := (finiteJetPrefix N K hKN).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (finiteJetPrefix_surjective N K hKN),finrank_top,Module.finrank_pi,Module.finrank_pi] at h
  simp only [Fintype.card_fin] at h
  omega

/-- A scalar series of order `m` kills exactly those jets whose first `N-m` coefficients vanish. -/
theorem ker_scalarTaylorJetMap_eq_prefix (f : PowerSeries ℂ) (m : ℕ) (hf : f.order = m) (N : ℕ) :
    LinearMap.ker (scalarTaylorJetMap f N) = LinearMap.ker (finiteJetPrefix N (N-m) (Nat.sub_le _ _)) := by
  ext v
  rw [LinearMap.mem_ker,LinearMap.mem_ker]
  change seriesFiniteJet N (f*finiteJetSeries N v) = 0 ↔ _
  rw [seriesFiniteJet_eq_zero_iff_order,PowerSeries.order_mul,hf]
  have ho : (N : ℕ∞) ≤ (m : ℕ∞)+(finiteJetSeries N v).order ↔
      ((N-m : ℕ) : ℕ∞) ≤ (finiteJetSeries N v).order := by
    rw [ENat.natCast_sub,tsub_le_iff_right,add_comm]
  rw [ho,← seriesFiniteJet_eq_zero_iff_order,seriesFiniteJet_finiteJetSeries_prefix N (N-m) (Nat.sub_le _ _)]

/-- The dimension of a scalar Taylor kernel is the minimum of truncation length and vanishing order. -/
theorem finrank_ker_scalarTaylorJetMap (f : PowerSeries ℂ) (m : ℕ) (hf : f.order = m) (N : ℕ) :
    Module.finrank ℂ (LinearMap.ker (scalarTaylorJetMap f N)) = min N m := by
  rw [ker_scalarTaylorJetMap_eq_prefix f m hf,finrank_ker_finiteJetPrefix]
  omega

/-- A nonzero scalar series has its full vanishing order as kernel dimension at every sufficiently long truncation. -/
theorem finrank_ker_scalarTaylorJetMap_of_order_le (f : PowerSeries ℂ) (m : ℕ)
    (hf : f.order = m) (N : ℕ) (hN : m ≤ N) :
    Module.finrank ℂ (LinearMap.ker (scalarTaylorJetMap f N)) = m := by
  rw [finrank_ker_scalarTaylorJetMap f m hf,min_eq_right hN]

/-- Every nonzero scalar series eventually has Taylor nullity equal to its finite order. -/
theorem eventually_finrank_ker_scalarTaylorJetMap (f : PowerSeries ℂ) (hf : f ≠ 0) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Module.finrank ℂ (LinearMap.ker (scalarTaylorJetMap f N)) = f.order.toNat := by
  refine Filter.eventually_atTop.mpr ⟨f.order.toNat,fun N hN => ?_⟩
  exact finrank_ker_scalarTaylorJetMap_of_order_le f f.order.toNat (PowerSeries.coe_toNat_order hf).symm N hN

/-- The identically zero scalar series kills the entire finite Taylor space. -/
theorem finrank_ker_scalarTaylorJetMap_zero (N : ℕ) :
    Module.finrank ℂ (LinearMap.ker (scalarTaylorJetMap 0 N)) = N := by
  rw [scalarTaylorJetMap_zero,LinearMap.ker_zero,finrank_top,Module.finrank_pi,Fintype.card_fin]

end NLS.ComplexAnalysis
