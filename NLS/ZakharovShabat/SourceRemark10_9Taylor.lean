import NLS.ZakharovShabat.SourceMidpointQuotientTaylorMajorant
import NLS.ZakharovShabat.SourceFreeSineQuotientRefined

/-!
# The exact quarter-exponent expansion underlying Remark 10.9

On every original disk, subtracting the signed sum
`γ_m² / (8(τ_m-z)²)` leaves a locally uniformly bounded ℓ(p/4)
supremum sequence. The printed replacement by an integer-lattice
kernel and the claim of optimality are separate source-audit questions.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal disk supremum after subtracting the exact linear term. -/
def sourceMidpointQuotientTaylorSup (hp : p ≠ ⊤) (hp1 : 1 < p)
    (D : ℤ → Set ℂ) (ψ : CoeffPair p) (n : ℤ) : ℝ :=
  sSup ((fun z => ‖sourceMidpointQuotient hp hp1 ψ n z-1-
    sourceMidpointQuotientLinearTerm hp hp1 ψ n z‖) '' D n)

/-- The reciprocal-square convolution norm used in the gap-row bound. -/
def sourceSquaredGapRowNormConstant (hp : p ≠ ⊤) (hp1 : 1 < p) : ℝ :=
  ‖squaredReciprocalKernel (min 1 (p.toReal/2))
    (lt_min (by norm_num : (1/2:ℝ)<1) (by
      have hpr : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
      linarith))‖

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}

/-- A physical row majorant gives the actual full-disk supremum coefficient. -/
theorem SourceIsolatingNeighborhoods.midpoint_taylor_sup_of_row
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (S : Coeff (ENNReal.ofReal (p.toReal/2)))
    (hS : ∀ n : ℤ, S n = ((∑' m, sourceSquaredGapReciprocalTerm hp hp1 ψ n m : ℝ):ℂ))
    {H : ℝ} (hH : ‖S‖ ≤ H) :
    ∃ E : Coeff (p/4),
      (∀ n, E n = (sourceMidpointQuotientTaylorSup hp hp1 D ψ n : ℂ)) ∧
      ‖E‖ ≤ midpointQuotientTaylorConstant c H*H^2 ∧
      ∀ n : ℤ, ∀ z ∈ D n,
        ‖sourceMidpointQuotient hp hp1 ψ n z-1-sourceMidpointQuotientLinearTerm hp hp1 ψ n z‖ ≤
          sourceMidpointQuotientTaylorSup hp hp1 D ψ n := by
  obtain ⟨B,hB,hpoint⟩ := h.midpoint_taylor_majorant_of_row ψ hψ S hS hH
  have hn (n : ℤ) : (D n).Nonempty := by
    obtain ⟨a,r,hr,he⟩ := h.discs n
    rw [he]
    exact nonempty_ball.mpr hr
  have hb (n : ℤ) : BddAbove ((fun z => ‖sourceMidpointQuotient hp hp1 ψ n z-1-
      sourceMidpointQuotientLinearTerm hp hp1 ψ n z‖) '' D n) := by
    refine ⟨‖B n‖,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact hpoint n z hz
  have hle (n : ℤ) (z : ℂ) (hz : z ∈ D n) :
      ‖sourceMidpointQuotient hp hp1 ψ n z-1-sourceMidpointQuotientLinearTerm hp hp1 ψ n z‖ ≤
        sourceMidpointQuotientTaylorSup hp hp1 D ψ n := le_csSup (hb n) ⟨z,hz,rfl⟩
  have hnonneg (n : ℤ) : 0 ≤ sourceMidpointQuotientTaylorSup hp hp1 D ψ n := by
    obtain ⟨z,hz⟩ := hn n
    exact (norm_nonneg _).trans (hle n z hz)
  have hbound (n : ℤ) : ‖(sourceMidpointQuotientTaylorSup hp hp1 D ψ n : ℂ)‖ ≤ ‖B n‖ := by
    rw [Complex.norm_real,Real.norm_of_nonneg (hnonneg n)]
    apply csSup_le ((hn n).image _)
    rintro _ ⟨z,hz,rfl⟩
    exact hpoint n z hz
  let E : Coeff (p/4) := ⟨fun n => (sourceMidpointQuotientTaylorSup hp hp1 D ψ n : ℂ),
    (lp.memℓp B).mono' hbound⟩
  refine ⟨E,fun _ => rfl,?_,hle⟩
  exact (lp.norm_mono (ENNReal.div_pos (zero_lt_one.trans hp1).ne' (by norm_num)).ne' hbound).trans hB

/-- One original-source neighborhood has a common quarter-exponent supremum bound. -/
theorem SourceIsolatingNeighborhoods.uniform_midpoint_taylor_sup
    (h : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφ : φ ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ V ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ T, ∃ E : Coeff (p/4),
        (∀ n, E n = (sourceMidpointQuotientTaylorSup hp hp1 D ψ n : ℂ)) ∧ ‖E‖ ≤ K ∧
        ∀ n : ℤ, ∀ z ∈ D n,
          ‖sourceMidpointQuotient hp hp1 ψ n z-1-sourceMidpointQuotientLinearTerm hp hp1 ψ n z‖ ≤
            sourceMidpointQuotientTaylorSup hp hp1 D ψ n := by
  obtain ⟨Vg,hVg,hφg,R,_,hg⟩ := exists_local_sourcePeriodicSquaredGapCoeff_bound hp hp1 φ
  let H := R^2*sourceSquaredGapRowNormConstant hp hp1
  have hK : 0 ≤ midpointQuotientTaylorConstant c H*H^2 :=
    mul_nonneg (midpointQuotientTaylorConstant_nonneg c H) (sq_nonneg H)
  refine ⟨V ∩ Vg,hV.inter hVg,⟨hφ,hφg⟩,inter_subset_left,
    midpointQuotientTaylorConstant c H*H^2,hK,?_⟩
  intro ψ hψ
  obtain ⟨S,hS,hSn⟩ := exists_sourceSquaredGapPhysicalRows hp hp1 ψ
  have hSn' : ‖S‖ ≤ H := by
    apply hSn.trans
    exact mul_le_mul_of_nonneg_right (hg ψ hψ.2) (lp.norm_nonneg' _)
  exact h.midpoint_taylor_sup_of_row ψ hψ.1 S (fun n => (hS n).2) hSn'

/-- The exact Taylor remainder on the unchanged common almost-real domain.
The original isolating disks are selected before the smaller bound neighborhood. -/
theorem SourceLemma10_8Estimates.midpoint_taylor
    {W : Set (CoeffPair p)} (h : SourceLemma10_8Estimates hp hp1 W)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ D c, SourceCanonicalRootNeighborhoods hp hp1 V D c ∧
        ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ V ∧
          ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ T, ∃ E : Coeff (p/4),
            (∀ n, E n = (sourceMidpointQuotientTaylorSup hp hp1 D ψ n : ℂ)) ∧ ‖E‖ ≤ K ∧
            ∀ n : ℤ, ∀ z ∈ D n,
              ‖sourceMidpointQuotient hp hp1 ψ n z-1-sourceMidpointQuotientLinearTerm hp hp1 ψ n z‖ ≤
                sourceMidpointQuotientTaylorSup hp hp1 D ψ n := by
  obtain ⟨V,ho,hc,hφV,hVW,D,c,hD,_⟩ := h.neighborhoods φ hφ
  exact ⟨V,ho,hc,hφV,hVW,D,c,hD,
    hD.toSourceIsolatingNeighborhoods.uniform_midpoint_taylor_sup ho φ hφV⟩

/-- Every source in one common almost-real neighborhood has the actual ℓ(p/4) expansion. -/
theorem sourceRemark10_9_exactTaylor (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_8Estimates hp hp1 W ∧
      ∀ φ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ W ∧
        ∃ D c, SourceCanonicalRootNeighborhoods hp hp1 V D c ∧
          ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ V ∧
            ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ T, ∃ E : Coeff (p/4),
              (∀ n, E n = (sourceMidpointQuotientTaylorSup hp hp1 D ψ n : ℂ)) ∧ ‖E‖ ≤ K ∧
              ∀ n : ℤ, ∀ z ∈ D n,
                ‖sourceMidpointQuotient hp hp1 ψ n z-1-sourceMidpointQuotientLinearTerm hp hp1 ψ n z‖ ≤
                  sourceMidpointQuotientTaylorSup hp hp1 D ψ n := by
  obtain ⟨W,ho,hc,hr,h⟩ := sourceLemma10_8_estimates hp hp1
  exact ⟨W,ho,hc,hr,h,h.midpoint_taylor⟩

end NLS.ZakharovShabat
