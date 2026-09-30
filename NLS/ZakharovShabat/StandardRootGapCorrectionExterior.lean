import NLS.ZakharovShabat.RelativeProductsExteriorLimit
import NLS.ZakharovShabat.SourceStandardRootProductFactors

/-!
# Standard-root gap corrections at exterior infinity

Outside fixed free spectral discs, the free resolvent sends both midpoint
displacements and gaps to zero in ℓ¹. Once the midpoint error is at most
one half, the total squared-gap radicand is bounded by the square of the
absolute gap-resolvent sum. The actual principal-square-root correction
product therefore tends to one in every separated direction.
-/

noncomputable section
open Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The gap radicand in the standard root with midpoint sequence `τ`. -/
def spectralGapRadicand (τ γ : ℤ → ℂ) (z : ℂ) (m : ℤ) : ℂ :=
  (γ m)^2 / (4*(τ m-z)^2)

/-- The principal-square-root correction to the linear midpoint factor. -/
def standardRootGapCorrection (τ γ : ℤ → ℂ) (z : ℂ) (m : ℤ) : ℂ :=
  Complex.sqrt (1-spectralGapRadicand τ γ z m)

/-- A midpoint perturbation of relative size at most one half leaves
enough separation to bound the radicand by the free gap quotient squared. -/
theorem norm_spectralGapRadicand_le (τ γ : ℤ → ℂ) (z : ℂ)
    (hz : z ∉ freeLattice) (m : ℤ)
    (hτ : ‖(τ m-(Real.pi : ℂ)*m)/(z-(Real.pi : ℂ)*m)‖ ≤ 1/2) :
    ‖spectralGapRadicand τ γ z m‖ ≤ ‖γ m/(z-(Real.pi : ℂ)*m)‖^2 := by
  have hd : 0 < ‖z-(Real.pi : ℂ)*m‖ := by
    apply norm_pos_iff.mpr
    intro he
    exact hz ⟨m, (sub_eq_zero.mp he).symm⟩
  have ht : ‖τ m-(Real.pi : ℂ)*m‖ ≤ ‖z-(Real.pi : ℂ)*m‖/2 := by
    rw [norm_div] at hτ
    have h := (div_le_iff₀ hd).mp hτ
    linarith
  have htri : ‖z-(Real.pi : ℂ)*m‖ ≤ ‖τ m-z‖+‖τ m-(Real.pi : ℂ)*m‖ := by
    calc
      _ = ‖-(τ m-z)+(τ m-(Real.pi : ℂ)*m)‖ := by congr 1; ring
      _ ≤ _ := by simpa only [norm_neg] using norm_add_le (-(τ m-z)) _
  have htpos : 0 < ‖τ m-z‖ := by linarith
  have hsq : ‖z-(Real.pi : ℂ)*m‖^2 ≤ 4*‖τ m-z‖^2 := by
    nlinarith [sq_nonneg (‖τ m-z‖-‖z-(Real.pi : ℂ)*m‖/2)]
  simp only [spectralGapRadicand, norm_div, norm_pow, norm_mul, Complex.norm_ofNat]
  rw [div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hd) hsq

/-- The ℓ¹ gap-resolvent sum controls the complete radicand sum. -/
theorem spectralGapRadicand_summable_bound (hp : p ≠ ⊤)
    (τ γ : ℤ → ℂ) (hγ : Memℓp γ p) (z : ℂ) (hz : z ∉ freeLattice)
    (hτ : ∀ m : ℤ, ‖(τ m-(Real.pi : ℂ)*m)/(z-(Real.pi : ℂ)*m)‖ ≤ 1/2) :
    Summable (fun m => ‖spectralGapRadicand τ γ z m‖) ∧
      (∑' m, ‖spectralGapRadicand τ γ z m‖) ≤
        (∑' m : ℤ, ‖γ m/(z-(Real.pi : ℂ)*m)‖)^2 := by
  have hg : Summable (fun m : ℤ => ‖γ m/(z-(Real.pi : ℂ)*m)‖) := by
    simpa only [add_sub_cancel_right] using
      summable_norm_spectralRelativeDisplacement hp
        (fun m => γ m+(Real.pi : ℂ)*m) (by simpa only [add_sub_cancel_right] using hγ) z hz
  let B := ∑' m : ℤ, ‖γ m/(z-(Real.pi : ℂ)*m)‖
  have hpoint (m : ℤ) : ‖spectralGapRadicand τ γ z m‖ ≤
      B*‖γ m/(z-(Real.pi : ℂ)*m)‖ := by
    have hm : ‖γ m/(z-(Real.pi : ℂ)*m)‖ ≤ B :=
      hg.le_tsum m (fun _ _ => norm_nonneg _)
    calc
      _ ≤ ‖γ m/(z-(Real.pi : ℂ)*m)‖^2 := norm_spectralGapRadicand_le τ γ z hz m (hτ m)
      _ ≤ _ := by nlinarith [norm_nonneg (γ m/(z-(Real.pi : ℂ)*m))]
  have hmajor := hg.mul_left B
  have hsum := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hmajor
  refine ⟨hsum, (hsum.tsum_le_tsum hpoint hmajor).trans_eq ?_⟩
  rw [tsum_mul_left]
  change B*B = B^2
  ring

/-- On separated escaping paths, midpoint displacement is uniformly small
over all signed indices. -/
theorem eventually_midpoint_relative_norm_le_half_of_separated
    {α : Type*} {l : Filter α} (hp : p ≠ ⊤) (τ : ℤ → ℂ)
    (hτ : Memℓp (fun m => τ m-(Real.pi : ℂ)*m) p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (m : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*m‖) :
    ∀ᶠ i in l, ∀ m : ℤ,
      ‖(τ m-(Real.pi : ℂ)*m)/(z i-(Real.pi : ℂ)*m)‖ ≤ 1/2 := by
  have ht := tendsto_tsum_norm_relativeDisplacement_of_separated hp τ hτ z hescape hr hrπ hsep
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))] with i hi m
  have hs := summable_norm_spectralRelativeDisplacement hp τ hτ (z i)
    (notMem_freeLattice_of_separated hr (hsep i))
  exact (hs.le_tsum m (fun _ _ => norm_nonneg _)).trans hi.le

/-- The complete radicand is eventually absolutely summable, and its
absolute sum tends to zero outside fixed free discs. -/
theorem spectralGapRadicand_exterior_limit {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (τ γ : ℤ → ℂ)
    (hτ : Memℓp (fun m => τ m-(Real.pi : ℂ)*m) p) (hγ : Memℓp γ p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (m : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*m‖) :
    (∀ᶠ i in l, Summable (fun m => ‖spectralGapRadicand τ γ (z i) m‖)) ∧
      Tendsto (fun i => ∑' m, ‖spectralGapRadicand τ γ (z i) m‖) l (𝓝 0) := by
  have hmid := eventually_midpoint_relative_norm_le_half_of_separated hp τ hτ z hescape hr hrπ hsep
  have hb : ∀ᶠ i in l,
      Summable (fun m => ‖spectralGapRadicand τ γ (z i) m‖) ∧
        (∑' m, ‖spectralGapRadicand τ γ (z i) m‖) ≤
          (∑' m : ℤ, ‖γ m/(z i-(Real.pi : ℂ)*m)‖)^2 := by
    filter_upwards [hmid] with i hi
    exact spectralGapRadicand_summable_bound hp τ γ hγ (z i)
      (notMem_freeLattice_of_separated hr (hsep i)) hi
  refine ⟨hb.mono (fun _ h => h.1), ?_⟩
  have hg := tendsto_tsum_norm_relativeDisplacement_of_separated hp
    (fun m => γ m+(Real.pi : ℂ)*m) (by simpa only [add_sub_cancel_right] using hγ)
    z hescape hr hrπ hsep
  have hg' : Tendsto (fun i => (∑' m : ℤ, ‖γ m/(z i-(Real.pi : ℂ)*m)‖)^2) l (𝓝 0) := by
    simpa only [add_sub_cancel_right, zero_pow (by norm_num : 2 ≠ 0)] using hg.pow 2
  exact squeeze_zero' (Eventually.of_forall (fun _ => tsum_nonneg (fun _ => norm_nonneg _)))
    (hb.mono (fun _ h => h.2)) hg'

/-- The actual principal-square-root correction product tends to one. -/
theorem standardRootGapCorrection_exterior_limit {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (τ γ : ℤ → ℂ)
    (hτ : Memℓp (fun m => τ m-(Real.pi : ℂ)*m) p) (hγ : Memℓp γ p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (m : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*m‖) :
    (∀ᶠ i in l, Summable (fun m => ‖standardRootGapCorrection τ γ (z i) m-1‖)) ∧
      Tendsto (fun i => ∏' m, standardRootGapCorrection τ γ (z i) m) l (𝓝 1) := by
  obtain ⟨hs, ht⟩ := spectralGapRadicand_exterior_limit hp τ γ hτ hγ z hescape hr hrπ hsep
  have hb (i : α) (hi : Summable (fun m => ‖spectralGapRadicand τ γ (z i) m‖)) :
      Summable (fun m => ‖standardRootGapCorrection τ γ (z i) m-1‖) ∧
        (∑' m, ‖standardRootGapCorrection τ γ (z i) m-1‖) ≤
          ∑' m, ‖spectralGapRadicand τ γ (z i) m‖ := by
    have hle (m : ℤ) : ‖standardRootGapCorrection τ γ (z i) m-1‖ ≤
        ‖spectralGapRadicand τ γ (z i) m‖ := norm_sqrt_one_sub_sub_one_le _
    have hsum := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hi
    exact ⟨hsum, hsum.tsum_le_tsum hle hi⟩
  have hsum := hs.mono (fun i hi => (hb i hi).1)
  refine ⟨hsum, ?_⟩
  have herr : Tendsto (fun i => ∑' m, ‖standardRootGapCorrection τ γ (z i) m-1‖) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => tsum_nonneg (fun _ => norm_nonneg _)))
      (hs.mono (fun i hi => (hb i hi).2)) ht
  have hprod := tendsto_tprod_one_add_of_tsum_norm_tendsto_zero
    (fun i m => standardRootGapCorrection τ γ (z i) m-1) hsum herr
  simpa only [add_sub_cancel] using hprod

end NLS.ZakharovShabat
