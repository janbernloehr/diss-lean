import NLS.ZakharovShabat.SpectralLocalization
import NLS.ZakharovShabat.SourceNeumannProof
import NLS.ZakharovShabat.SourceSection3Setup
import NLS.ZakharovShabat.SourceLemma3_4

/-! # The original-norm proof of Corollary 3.5

Smallness of the squared potential/free-resolvent operator gives the actual
full-domain inverse and paired Neumann series. Concrete Fourier-tail
neighborhoods give the printed quarter/half bounds in the original pair
norm, with one connected neighborhood for all larger spectral cutoffs.
The source's mixed box boundaries and open disks are retained exactly.
-/

noncomputable section
open scoped ENNReal
open Filter Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full-domain pencil factorization in the original pair coordinates. -/
theorem sourceSpectralPencil_factorization (hp : p ≠ ⊤) (φ : CoeffPair p)
    (z : ℂ) (hz : z ∉ freeLattice) (a : WeightedCoeffPair (Weight.sobolev 1) p) :
    sourceSpectralPencil hp φ z a =
      (CoeffPair.toMax p).symm (freePencil z (WeightedCoeffPair.toMax (Weight.sobolev 1) p a)) -
        (sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz)
          ((CoeffPair.toMax p).symm (freePencil z (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))) := by
  apply (CoeffPair.toMax p).injective
  change (CoeffPair.toMax p) ((CoeffPair.toMax p).symm
    (spectralPencil hp (CoeffPair.toMax p φ) z (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, map_sub,
    ContinuousLinearEquiv.apply_symm_apply]
  change _ = _ - (CoeffPair.toMax p)
    (sourcePotentialFromL1 φ (sourceFreeResolventToL1 hp z hz _))
  rw [toMax_sourcePotentialFreeResolvent_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact spectralPencil_factorization hp (CoeffPair.toMax p φ) z hz _

/-- Original-norm smallness of the square gives a genuine full-domain inverse. -/
theorem mem_sourceResolventSet_of_square_norm (hp : p ≠ ⊤) (φ : CoeffPair p)
    (z : ℂ) (hz : z ∉ freeLattice)
    (h : ‖((sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz))^2‖ < 1) :
    z ∈ sourceResolventSet hp φ := by
  let T := (sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz)
  let Q : CoeffPair p →L[ℂ] CoeffPair p := 1-T
  let F := (WeightedCoeffPair.toMax (Weight.sobolev 1) p).trans
    ((freePencilEquiv (p := p) z hz).trans (CoeffPair.toMax p).symm)
  have hQ : Function.Bijective Q :=
    ⟨Function.LeftInverse.injective (SquaredNeumann.correction_left T h),
      Function.RightInverse.surjective (SquaredNeumann.correction_right T h)⟩
  have he : sourceSpectralPencil hp φ z = Q.comp F.toContinuousLinearMap := by
    ext a : 1
    exact sourceSpectralPencil_factorization hp φ z hz a
  change Function.Bijective (sourceSpectralPencil hp φ z)
  rw [he]
  exact hQ.comp F.bijective

/-- The literal squared Neumann formula uses the actual original-norm resolvent. -/
theorem sourceResolvent_squared_formula (hp : p ≠ ⊤) (φ : CoeffPair p)
    (z : ℂ) (hz : z ∉ freeLattice)
    (h : ‖((sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz))^2‖ < 1) :
    sourceResolvent hp φ z = sourceFreeResolvent hp z hz *
      SquaredNeumann.correction ((sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz)) h := by
  let T := (sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz)
  have hid := sourceResolvent_comp_one_sub_potentialFreeResolvent hp φ z hz
    (mem_sourceResolventSet_of_square_norm hp φ z hz h)
  change sourceResolvent hp φ z * (1-T) = sourceFreeResolvent hp z hz at hid
  calc
    _ = sourceResolvent hp φ z * ((1-T)*SquaredNeumann.correction T h) := by
      rw [SquaredNeumann.mul_correction, mul_one]
    _ = _ := by rw [← mul_assoc, hid]

/-- The paired even/odd Neumann series converges when only the square is small. -/
theorem hasSum_sourceResolvent_squared (hp : p ≠ ⊤) (φ : CoeffPair p)
    (z : ℂ) (hz : z ∉ freeLattice)
    (h : ‖((sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz))^2‖ < 1) :
    let T := (sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz)
    HasSum (fun n : ℕ => (sourceFreeResolvent hp z hz*(1+T))*(T^2)^n)
      (sourceResolvent hp φ z) := by
  dsimp only
  rw [sourceResolvent_squared_formula hp φ z hz h, SquaredNeumann.correction, ← mul_assoc]
  exact (SquaredNeumann.evenCorrection_hasSum _ h).mul_left _

/-- The squared inverse formula transfers the explicit free compactness proof. -/
theorem isCompactOperator_sourceResolvent_from_square (hp : p ≠ ⊤) (φ : CoeffPair p)
    (z : ℂ) (hz : z ∉ freeLattice)
    (h : ‖((sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz))^2‖ < 1) :
    IsCompactOperator (sourceResolvent hp φ z) := by
  rw [sourceResolvent_squared_formula hp φ z hz h]
  exact (isCompactOperator_sourceFreeResolvent_from_cutoffs hp z hz).comp_clm _


/-- Boundary-retaining Fourier tails as operators in the source pair norm. -/
def sourceFourierTailCLM (N : ℕ) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.conjContinuousAlgEquiv (pairFourierTailCLM N)

@[simp] theorem sourceFourierTailCLM_apply (N : ℕ) (φ : CoeffPair p) :
    sourceFourierTailCLM (p := p) N φ = sourceFourierTail N φ := rfl

@[simp] theorem sourceFourierTail_zero_potential (N : ℕ) :
    sourceFourierTail N (0 : CoeffPair p) = 0 :=
  (sourceFourierTailCLM (p := p) N).map_zero

/-- Bounding the full potential and one symmetric tail gives a useful neighborhood. -/
def sourceFrequencyNeighborhood (N : ℕ) (M δ : ℝ) : Set (CoeffPair p) :=
  Metric.ball 0 M ∩ (sourceFourierTailCLM (p := p) N) ⁻¹' Metric.ball 0 δ

@[simp] theorem mem_sourceFrequencyNeighborhood (N : ℕ) (M δ : ℝ) (ψ : CoeffPair p) :
    ψ ∈ sourceFrequencyNeighborhood N M δ ↔ ‖ψ‖ < M ∧ ‖sourceFourierTail N ψ‖ < δ := by
  simp [sourceFrequencyNeighborhood]

theorem isOpen_sourceFrequencyNeighborhood (N : ℕ) (M δ : ℝ) :
    IsOpen (sourceFrequencyNeighborhood (p := p) N M δ) :=
  Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage (sourceFourierTailCLM (p := p) N).continuous)

theorem convex_sourceFrequencyNeighborhood (N : ℕ) (M δ : ℝ) :
    Convex ℝ (sourceFrequencyNeighborhood (p := p) N M δ) :=
  (convex_ball (0 : CoeffPair p) M).inter
    ((convex_ball (0 : CoeffPair p) δ).linear_preimage
      ((sourceFourierTailCLM (p := p) N).restrictScalars ℝ).toLinearMap)

theorem zero_mem_sourceFrequencyNeighborhood (N : ℕ) {M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ) :
    (0 : CoeffPair p) ∈ sourceFrequencyNeighborhood N M δ := by
  change 0 ∈ Metric.ball 0 M ∩ (sourceFourierTailCLM (p := p) N) ⁻¹' Metric.ball 0 δ
  simpa using And.intro hM hδ

/-- An open convex neighborhood containing zero has an arbitrarily small
squared Neumann bound at all sufficiently large Fourier indices. -/
theorem exists_uniform_sourceFrequencyNeighborhood (hp : p ≠ ⊤) (φ : CoeffPair p)
    {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ‖ψ‖ < ‖φ‖ + 1) ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        ‖ψ‖ * ((64 * p.toReal ^ 2 / r ^ 2) *
          (‖ψ‖ / |(n : ℝ)| ^ (1 / p.toReal) + ‖sourceFourierTail n.natAbs ψ‖)) ≤ ε := by
  let M := ‖φ‖ + 1
  let C := 64 * p.toReal ^ 2 / r ^ 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne' hp
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := ε / (2 * M * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ht := (tendsto_sourceFourierTail hp φ).norm
  simp only [norm_zero] at ht
  have hevent : ∀ᶠ N : ℕ in atTop,
      ‖sourceFourierTail N φ‖ < δ ∧ M / (N : ℝ) ^ (1 / p.toReal) < δ :=
    (ht.eventually_lt_const hδ).and ((tendsto_frequency_reciprocal_zero hp M).eventually_lt_const hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let U : Set (CoeffPair p) := sourceFrequencyNeighborhood N M δ
  refine ⟨N, U, isOpen_sourceFrequencyNeighborhood N M δ, convex_sourceFrequencyNeighborhood N M δ,
    ?_, zero_mem_sourceFrequencyNeighborhood N hM hδ, ?_, ?_⟩
  · exact (mem_sourceFrequencyNeighborhood N M δ φ).mpr ⟨by dsimp [M]; linarith, (hN N le_rfl).1⟩
  · intro ψ hψ
    exact ((mem_sourceFrequencyNeighborhood N M δ ψ).mp hψ).1
  · intro ψ hψ n hn
    obtain ⟨hψM, hψT⟩ := (mem_sourceFrequencyNeighborhood N M δ ψ).mp hψ
    have htail : ‖sourceFourierTail n.natAbs ψ‖ ≤ δ :=
      (norm_sourceFourierTail_antitone hp ψ hn).trans hψT.le
    have hrec : ‖ψ‖ / |(n : ℝ)| ^ (1 / p.toReal) ≤ δ := by
      have he : |(n : ℝ)| = (n.natAbs : ℝ) := by simp only [Nat.cast_natAbs, Int.cast_abs]
      rw [he]
      exact (div_le_div_of_nonneg_right hψM.le (by positivity)).trans (hN n.natAbs hn).2.le
    change ‖ψ‖ * (C * (_ + _)) ≤ _
    calc
      _ ≤ M * (C * (δ + δ)) := by gcongr
      _ = ε := by dsimp [δ]; field_simp; ring

/-- Uniform squared Neumann smallness in the actual source operator norm. -/
theorem exists_uniform_sourcePotentialFreeResolvent_square (hp : p ≠ ⊤)
    (φ : CoeffPair p) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ‖ψ‖ < ‖φ‖ + 1) ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ verticalStrip n r,
        ‖((sourcePotentialFromL1 ψ).comp (sourceFreeResolventToL1 hp z
          (notMem_freeLattice_of_mem_verticalStrip hr hrπ hz)))^2‖ ≤ ε := by
  obtain ⟨N,U,ho,hc,hφ,h0,hnorm,hsmall⟩ :=
    exists_uniform_sourceFrequencyNeighborhood hp φ hr hε
  refine ⟨N,U,ho,hc,hφ,h0,hnorm,?_⟩
  intro ψ hψ n hn z hz
  apply (norm_sourcePotentialFreeResolvent_sq_le hp ψ z _).trans
  exact (mul_le_mul_of_nonneg_left
    (norm_sourceDoubleResolvent_le_verticalStrip hp ψ z _ hr hrπ hz) (norm_nonneg ψ)).trans
      (hsmall ψ hψ n hn)

/-- The printed quarter bound at the source and half bound on one connected neighborhood. -/
theorem exists_source_quarter_half_strips (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ n : ℤ, N < n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ verticalStrip n (Real.pi/4),
        ‖((sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z
          (notMem_freeLattice_of_mem_verticalStrip (by positivity) le_rfl hz)))^2‖ ≤ 1/4) ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N < n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ verticalStrip n (Real.pi/4),
        ‖((sourcePotentialFromL1 ψ).comp (sourceFreeResolventToL1 hp z
          (notMem_freeLattice_of_mem_verticalStrip (by positivity) le_rfl hz)))^2‖ ≤ 1/2 := by
  obtain ⟨N,U,ho,hc,hφ,h0,_,hsmall⟩ :=
    exists_uniform_sourcePotentialFreeResolvent_square hp φ
      (r := Real.pi/4) (by positivity) le_rfl (ε := 1/4) (by norm_num)
  refine ⟨N,U,ho,hc,⟨⟨0,h0⟩,hc.isPreconnected⟩,hφ,h0,?_,?_⟩
  · intro n hn z hz
    exact hsmall φ hφ n hn.le z hz
  · intro ψ hψ n hn z hz
    exact (hsmall ψ hψ n hn.le z hz).trans (by norm_num)

/-- Bounded source potentials have a uniform original-norm Neumann bound at large height. -/
theorem exists_sourcePotentialFreeResolvent_uniform_height (hp : p ≠ ⊤)
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    ∃ H : ℝ, 0 < H ∧ ∀ ψ : CoeffPair p, ‖ψ‖ ≤ M →
      ∀ z : ℂ, H ≤ |z.im| → ∀ hz : z ∉ freeLattice,
        ‖(sourcePotentialFromL1 ψ).comp (sourceFreeResolventToL1 hp z hz)‖ < ε := by
  obtain ⟨H,hH,hR⟩ := exists_sourceFreeResolventToL1_uniform_small hp (ε/M) (by positivity)
  refine ⟨H,hH,?_⟩
  intro ψ hψ z hz hz0
  calc
    _ ≤ ‖sourcePotentialFromL1 ψ‖*‖sourceFreeResolventToL1 hp z hz0‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ M*‖sourceFreeResolventToL1 hp z hz0‖ :=
      mul_le_mul_of_nonneg_right ((norm_sourcePotentialFromL1_le ψ).trans hψ) (norm_nonneg _)
    _ < M*(ε/M) := mul_lt_mul_of_pos_left (hR z hz hz0) hM
    _ = ε := by field_simp

/-- One positive cutoff controls both high imaginary parts and distant strips in the source norm. -/
theorem exists_source_square_uniform_height_and_strips (hp : p ≠ ⊤)
    (φ : CoeffPair p) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), 0 < N ∧ IsOpen U ∧ Convex ℝ U ∧
      IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
      (∀ z : ℂ, (N : ℝ) ≤ |z.im| → ∀ hz : z ∉ freeLattice,
        ‖((sourcePotentialFromL1 ψ).comp (sourceFreeResolventToL1 hp z hz))^2‖ ≤ ε) ∧
      (∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ verticalStrip n r,
        ‖((sourcePotentialFromL1 ψ).comp (sourceFreeResolventToL1 hp z
          (notMem_freeLattice_of_mem_verticalStrip hr hrπ hz)))^2‖ ≤ ε) := by
  obtain ⟨N₀,U,ho,hc,hφ,h0,hnorm,hstrips⟩ :=
    exists_uniform_sourcePotentialFreeResolvent_square hp φ hr hrπ hε
  obtain ⟨H,hH,hheight⟩ := exists_sourcePotentialFreeResolvent_uniform_height hp
    (M := ‖φ‖+1) (ε := Real.sqrt ε) (by positivity) (Real.sqrt_pos.mpr hε)
  obtain ⟨K,hK⟩ := exists_nat_gt H
  let N := max N₀ K
  have hN₀ : N₀ ≤ N := le_max_left _ _
  have hHN : H ≤ (N : ℝ) := hK.le.trans (by exact_mod_cast (le_max_right N₀ K))
  have hN : 0 < N := by exact_mod_cast (hH.trans_le hHN)
  refine ⟨N,U,hN,ho,hc,⟨⟨0,h0⟩,hc.isPreconnected⟩,hφ,h0,?_⟩
  intro ψ hψ
  constructor
  · intro z hz hz0
    have hsmall := hheight ψ (hnorm ψ hψ).le z (hHN.trans hz) hz0
    rw [pow_two]
    apply (norm_mul_le _ _).trans
    nlinarith [Real.sq_sqrt hε.le, norm_nonneg
      ((sourcePotentialFromL1 ψ).comp (sourceFreeResolventToL1 hp z hz0))]
  · intro n hn z hz
    exact hstrips ψ hψ n (hN₀.trans hn) z hz

/-- One original-norm neighborhood controls the exact exterior for every larger cutoff. -/
theorem exists_source_spectralExterior_square_bound (hp : p ≠ ⊤)
    (φ : CoeffPair p) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧
      IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ψ ∈ U,
        ∀ z ∈ spectralExterior N r, ∃ hz : z ∉ freeLattice,
          ‖((sourcePotentialFromL1 ψ).comp (sourceFreeResolventToL1 hp z hz))^2‖ ≤ ε := by
  obtain ⟨N₀,U,hN₀,ho,hc,hconn,hφ,h0,hbounds⟩ :=
    exists_source_square_uniform_height_and_strips hp φ hr hrπ hε
  refine ⟨N₀,U,hN₀,ho,hc,hconn,hφ,h0,?_⟩
  intro N hN ψ hψ z hz
  rcases spectralExterior_height_or_strip N hrπ hz with hi | ⟨n,hn,hs⟩
  · have hNreal : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hi0 : z.im ≠ 0 := abs_pos.mp ((by exact_mod_cast hN₀ : (0 : ℝ) < N₀).trans (hNreal.trans_lt hi))
    exact ⟨notMem_freeLattice_of_im_ne_zero hi0,
      (hbounds ψ hψ).1 z (hNreal.trans hi.le) _⟩
  · exact ⟨notMem_freeLattice_of_mem_verticalStrip hr hrπ hs,
      (hbounds ψ hψ).2 n (hN.trans hn) z hs⟩

/-- The full source conclusion follows from the original-norm square bounds. -/
theorem sourceCorollary3_5_from_square (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧
      φ ∈ U ∧ 0 ∈ U ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ψ ∈ U,
        spectralExterior N (Real.pi/4) ⊆ sourceResolventSet hp ψ ∧
        AnalyticOnNhd ℂ (sourceResolvent hp ψ) (spectralExterior N (Real.pi/4)) ∧
        (∀ z ∈ spectralExterior N (Real.pi/4), IsCompactOperator (sourceResolvent hp ψ z)) ∧
        (sourceResolventSet hp ψ)ᶜ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi/4) := by
  obtain ⟨N₀,U,hN₀,ho,hc,hconn,hφ,h0,hbound⟩ :=
    exists_source_spectralExterior_square_bound hp φ
      (r := Real.pi/4) (by positivity) le_rfl (ε := 1/4) (by norm_num)
  refine ⟨N₀,U,hN₀,ho,hc,hconn,hφ,h0,?_⟩
  intro N hN ψ hψ
  have he : spectralExterior N (Real.pi/4) ⊆ sourceResolventSet hp ψ := by
    intro z hz
    obtain ⟨hz0,hsq⟩ := hbound N hN ψ hψ z hz
    exact mem_sourceResolventSet_of_square_norm hp ψ z hz0 (hsq.trans_lt (by norm_num))
  refine ⟨he,(analyticOnNhd_sourceResolvent hp ψ).mono he,?_,?_⟩
  · intro z hz
    obtain ⟨hz0,hsq⟩ := hbound N hN ψ hψ z hz
    exact isCompactOperator_sourceResolvent_from_square hp ψ z hz0 (hsq.trans_lt (by norm_num))
  · intro z hz
    by_contra hout
    exact hz (he hout)

/-- The source's real segment is compact and lies in every convex neighborhood of its endpoints. -/
theorem sourcePotentialSegment_compact_in_neighborhood (φ : CoeffPair p)
    {U : Set (CoeffPair p)} (hc : Convex ℝ U) (h0 : 0 ∈ U) (hφ : φ ∈ U) :
    IsCompact (segment ℝ (0 : CoeffPair p) φ) ∧ segment ℝ (0 : CoeffPair p) φ ⊆ U := by
  refine ⟨?_,hc.segment_subset h0 hφ⟩
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

end NLS.ZakharovShabat
