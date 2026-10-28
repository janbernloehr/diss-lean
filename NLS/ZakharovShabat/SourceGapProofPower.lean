import NLS.ZakharovShabat.SourceLemma6_8ProofSeries
import NLS.ZakharovShabat.ResonantGapMajorant
import NLS.ZakharovShabat.SourceLemma6_9

/-!
# The power comparison in the proof of Propositions 6.1 and 6.3

The second comparison on printed p.44 fails at p=4, even for arbitrarily
small original potentials with constant actual off-diagonal coefficients.
Its valid replacement uses 6^(p/2)/2. We apply it to the full strip
suprema and the original counted spectral pairs, with a common open
convex neighborhood and cutoff. The later summed inequality on p.44
is a separate assertion and is not refuted by this module.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceGapProofFactFour : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A balanced original period-two potential at exponent four and signed mode n. -/
def sourceGapProofPotential (n : ℤ) (t : ℂ) : CoeffPair 4 :=
  unitWeightedPairEquiv.symm (singleResonantPotential SpectralWeight.one n t t)

/-- The family is linear in its common amplitude. -/
theorem sourceGapProof_single_smul (n : ℤ) (t : ℂ) :
    singleResonantPotential (p := 4) SpectralWeight.one n t t =
      t • singleResonantPotential SpectralWeight.one n 1 1 := by
  apply weightedPair_ext <;> intro k <;> simp

/-- The original analytic coefficients are exactly zero, t and t on their contraction domain. -/
theorem sourceGapProof_actual_coefficients (n : ℤ) (t z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one
      (singleResonantPotential (p := 4) SpectralWeight.one n t t) n z hz‖ < 1) :
    sourceResonantAFunction (by norm_num) (sourceGapProofPotential n t) n z = 0 ∧
    sourceResonantBPlusFunction (by norm_num) (sourceGapProofPotential n t) n z = t ∧
    sourceResonantBMinusFunction (by norm_num) (sourceGapProofPotential n t) n z = t := by
  simp [sourceGapProofPotential,sourceResonantAFunction,sourceResonantBPlusFunction,
    sourceResonantBMinusFunction,sourceCorrectionEntryFunction,weightedCorrectionEntryExtension,
    correction_singleResonantSource (by norm_num) SpectralWeight.one n t t z hz h,
    show -n-n = -(2*n) by ring,show n+n = 2*n by ring]

/-- A constant on the entire closed strip has its exact norm as supremum. -/
theorem sourceGapProof_stripSup_const (n : ℤ) (f : ℂ → ℂ) (t : ℂ)
    (hf : ∀ z ∈ resonantStrip n, f z = t) : weightedStripSup SpectralWeight.one n f = ‖t‖ := by
  have h := weightedStripSup_bounds SpectralWeight.one n f ‖t‖ (by
    intro z hz; simp [hf z hz])
  apply le_antisymm h.2.1
  simpa [hf _ (center_mem_resonantStrip n)] using h.2.2 _ (center_mem_resonantStrip n)

/-- At p=4 the printed right side is 18*t^4, strictly below the left side 36*t^4. -/
theorem sourceGapProof_printed_scalar_failure (n : ℤ) (t : ℝ) (ht : 0 < t)
    (h : ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
      ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one
        (singleResonantPotential (p := 4) SpectralWeight.one n t t) n z hz‖ < 1) :
    let bp := sourceResonantBPlusFunction (by norm_num) (sourceGapProofPotential n t) n
    let bm := sourceResonantBMinusFunction (by norm_num) (sourceGapProofPotential n t) n
    (3 : ℝ)^(4/2 : ℝ) * ((weightedStripSup SpectralWeight.one n bp)^4 +
      (weightedStripSup SpectralWeight.one n bm)^4) <
      (6 : ℝ)^(4/2 : ℝ) * (weightedStripSup SpectralWeight.one n (fun z => bp z * bm z))^(4/2 : ℝ) := by
  dsimp only
  have hp := sourceGapProof_stripSup_const n _ (t:ℂ) (fun z hz => (sourceGapProof_actual_coefficients n t z hz (h z hz)).2.1)
  have hm := sourceGapProof_stripSup_const n _ (t:ℂ) (fun z hz => (sourceGapProof_actual_coefficients n t z hz (h z hz)).2.2)
  have hprod := sourceGapProof_stripSup_const n
    (fun z => sourceResonantBPlusFunction (by norm_num) (sourceGapProofPotential n t) n z *
      sourceResonantBMinusFunction (by norm_num) (sourceGapProofPotential n t) n z) ((t:ℂ)*(t:ℂ)) (by
    intro z hz
    rw [(sourceGapProof_actual_coefficients n t z hz (h z hz)).2.1,
      (sourceGapProof_actual_coefficients n t z hz (h z hz)).2.2])
  rw [hp,hm,hprod,norm_mul,Complex.norm_real,Real.norm_of_nonneg ht.le]
  norm_num [Real.rpow_two]
  nlinarith [pow_pos ht 4]

/-- An explicit admissible small amplitude exists at every index and arbitrarily near zero. -/
theorem sourceGapProof_exists_small_witness (n : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < Real.pi/16 ∧ ‖sourceGapProofPotential n t‖ < ε ∧
      ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one
          (singleResonantPotential (p := 4) SpectralWeight.one n t t) n z hz‖ ≤ 1/2 := by
  let C := Coeff.complementaryConstant 4 (by norm_num)
  let D := ‖singleResonantPotential (p := 4) SpectralWeight.one n 1 1‖
  let t := min (1/(4*(C*D+1))) (min (Real.pi/32) (ε/(2*(D+1))))
  have hC : 0 ≤ C := Coeff.complementaryConstant_nonneg _ _
  have hD : 0 ≤ D := norm_nonneg _
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1/(4*(C*D+1)) := min_le_left _ _
  have ht2 : t ≤ Real.pi/32 := (min_le_right _ _).trans (min_le_left _ _)
  have ht3 : t ≤ ε/(2*(D+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : C*(t*D) ≤ 1/4 := by
    have hprod := (le_div_iff₀ (show 0 < 4*(C*D+1) by positivity)).mp ht1
    nlinarith
  have hnormw : ‖singleResonantPotential (p := 4) SpectralWeight.one n t t‖ = t*D := by
    rw [sourceGapProof_single_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg ht.le]
  have hnorm : ‖sourceGapProofPotential n t‖ = t*D := by
    rw [sourceGapProofPotential,LinearIsometryEquiv.norm_map,hnormw]
  refine ⟨t,ht,by linarith [Real.pi_pos],?_,?_⟩
  · rw [hnorm]
    have hprod := (le_div_iff₀ (show 0 < 2*(D+1) by positivity)).mp ht3
    nlinarith
  · intro z hz
    have hbound := norm_weightedPotentialSquareInShift_le_coarse (by norm_num) SpectralWeight.one
      (singleResonantPotential (p := 4) SpectralWeight.one n t t) n z hz
    rw [hnormw] at hbound
    change _ ≤ (C*(t*D))^2 at hbound
    have hn : 0 ≤ C*(t*D) := by positivity
    nlinarith

/-- The correct power comparison uses 6^(P/2)/2, including exponents above two. -/
theorem sourceGapProof_correct_scalar {P x y s : ℝ} (hP : 0 ≤ P) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : 0 ≤ s) (hxy : s ≤ x*y) :
    (6 : ℝ)^(P/2)*s^(P/2) ≤ ((6 : ℝ)^(P/2)/2)*(x^P+y^P) := by
  have he (a : ℝ) (ha : 0 ≤ a) : (a^(P/2))^2 = a^P := by
    rw [← Real.rpow_two, ← Real.rpow_mul ha]
    congr 1
    ring
  have hm := sq_nonneg (x^(P/2)-y^(P/2))
  rw [sub_sq,he x hx,he y hy] at hm
  have hs' := Real.rpow_le_rpow hs hxy (by positivity : 0 ≤ P/2)
  rw [Real.mul_rpow hx hy] at hs'
  have hC : 0 ≤ (6:ℝ)^(P/2) := by positivity
  nlinarith [mul_nonneg hC (show 0 ≤ x^P+y^P-2*s^(P/2) by nlinarith)]


/-- Actual full coefficient suprema violate the p=4 display near zero beyond every common cutoff. -/
theorem sourceGapProof_failure_near_zero
    (U : Set (CoeffPair 4)) (hU : IsOpen U) (h0 : 0 ∈ U) (N : ℕ) :
    ∃ n : ℤ, (N:ℤ) ≤ n ∧ 0 < n ∧ ∃ t : ℝ, 0 < t ∧ t < Real.pi/16 ∧
      sourceGapProofPotential n t ∈ U ∧
      (∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift (by norm_num) SpectralWeight.one
          (singleResonantPotential (p := 4) SpectralWeight.one n t t) n z hz‖ ≤ 1/2) ∧
      (let bp := sourceResonantBPlusFunction (by norm_num) (sourceGapProofPotential n t) n
       let bm := sourceResonantBMinusFunction (by norm_num) (sourceGapProofPotential n t) n
       (3 : ℝ)^(4/2 : ℝ) * ((weightedStripSup SpectralWeight.one n bp)^4 +
         (weightedStripSup SpectralWeight.one n bm)^4) <
         (6 : ℝ)^(4/2 : ℝ) * (weightedStripSup SpectralWeight.one n (fun z => bp z * bm z))^(4/2 : ℝ)) := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  let n : ℤ := (N:ℤ)+1
  obtain ⟨t,ht,htπ,hnorm,hsmall⟩ := sourceGapProof_exists_small_witness n r hr
  refine ⟨n,by dsimp [n]; omega,by dsimp [n]; omega,t,ht,htπ,?_,hsmall,?_⟩
  · apply hball
    simpa only [Metric.mem_ball,dist_zero_right] using hnorm
  · exact sourceGapProof_printed_scalar_failure n t ht (fun z hz => (hsmall z hz).trans_lt (by norm_num))


/-- The corrected comparison applies to actual full-strip suprema of bounded functions. -/
theorem sourceGapProof_correct_full_suprema (n : ℤ) (f g : ℂ → ℂ) (P : ℝ) (hP : 0 ≤ P)
    (hf : BddAbove ((fun z => ‖f z‖) '' resonantStrip n))
    (hg : BddAbove ((fun z => ‖g z‖) '' resonantStrip n)) :
    (6:ℝ)^(P/2) * (weightedStripSup SpectralWeight.one n (fun z => f z*g z))^(P/2) ≤
      ((6:ℝ)^(P/2)/2) * ((weightedStripSup SpectralWeight.one n f)^P +
        (weightedStripSup SpectralWeight.one n g)^P) := by
  have hfle (z : ℂ) (hz : z ∈ resonantStrip n) : ‖f z‖ ≤ weightedStripSup SpectralWeight.one n f := by
    simpa only [weightedStripSup,SpectralWeight.one_apply,one_mul] using le_csSup hf ⟨z,hz,rfl⟩
  have hgle (z : ℂ) (hz : z ∈ resonantStrip n) : ‖g z‖ ≤ weightedStripSup SpectralWeight.one n g := by
    simpa only [weightedStripSup,SpectralWeight.one_apply,one_mul] using le_csSup hg ⟨z,hz,rfl⟩
  have hx : 0 ≤ weightedStripSup SpectralWeight.one n f :=
    (norm_nonneg _).trans (hfle _ (center_mem_resonantStrip n))
  have hy : 0 ≤ weightedStripSup SpectralWeight.one n g :=
    (norm_nonneg _).trans (hgle _ (center_mem_resonantStrip n))
  have hs := weightedStripSup_bounds SpectralWeight.one n (fun z => f z*g z)
    (weightedStripSup SpectralWeight.one n f * weightedStripSup SpectralWeight.one n g) (by
      intro z hz
      simp only [SpectralWeight.one_apply,one_mul,norm_mul]
      exact mul_le_mul (hfle z hz) (hgle z hz) (norm_nonneg _) hx)
  exact sourceGapProof_correct_scalar hP hx hy hs.1 hs.2.1

/-- Any actual nonnegative gap with the established factor-six square bound has the corrected power bound. -/
theorem sourceGapProof_correct_gap (n : ℤ) (f g : ℂ → ℂ) (P d : ℝ) (hP : 0 ≤ P) (hd : 0 ≤ d)
    (hf : BddAbove ((fun z => ‖f z‖) '' resonantStrip n))
    (hg : BddAbove ((fun z => ‖g z‖) '' resonantStrip n))
    (hgap : d^2 ≤ 6 * weightedStripSup SpectralWeight.one n (fun z => f z*g z)) :
    d^P ≤ ((6:ℝ)^(P/2)/2) * ((weightedStripSup SpectralWeight.one n f)^P +
      (weightedStripSup SpectralWeight.one n g)^P) := by
  have hs := sourceGapProof_correct_full_suprema n f g P hP hf hg
  have hs0 : 0 ≤ weightedStripSup SpectralWeight.one n (fun z => f z*g z) := by nlinarith [sq_nonneg d]
  have hb := Real.rpow_le_rpow (sq_nonneg d) hgap (by positivity : 0 ≤ P/2)
  have he : (d^2)^(P/2) = d^P := by
    rw [← Real.rpow_two,← Real.rpow_mul hd]
    congr 1
    ring
  rw [he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) hs0] at hb
  exact hb.trans hs


/-- The corrected comparison for the original counted spectral pair, including a double root. -/
theorem sourceGapProof_source_roots {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (φ : CoeffPair p) (n : ℤ) (x y : ℂ)
    (hc : SourceResonantStripControl hp φ n) (hr : SourceResonantRootPair hp φ n x y) :
    ‖x-y‖^p.toReal ≤ ((6:ℝ)^(p.toReal/2)/2) *
      ((weightedStripSup SpectralWeight.one n (sourceResonantBPlusFunction hp φ n))^p.toReal +
       (weightedStripSup SpectralWeight.one n (sourceResonantBMinusFunction hp φ n))^p.toReal) := by
  apply sourceGapProof_correct_gap n _ _ p.toReal ‖x-y‖ ENNReal.toReal_nonneg (norm_nonneg _)
  · exact ⟨Real.pi/16, by rintro _ ⟨z,hz,rfl⟩; exact hc.positive z hz⟩
  · exact ⟨Real.pi/16, by rintro _ ⟨z,hz,rfl⟩; exact hc.negative z hz⟩
  · simpa only [sourceResonantBProductSup,weightedStripSup,SpectralWeight.one_apply,one_mul]
      using hr.gap_le

/-- One original open convex neighborhood and signed cutoff support the corrected gap bound. -/
theorem sourceGapProof_uniform_source_roots {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ, ∀ n : ℤ, N ≤ n.natAbs →
        SourceResonantRootPair hp ψ n (ξ n) (η n) ∧
        ‖ξ n-η n‖^p.toReal ≤ ((6:ℝ)^(p.toReal/2)/2) *
          ((weightedStripSup SpectralWeight.one n (sourceResonantBPlusFunction hp ψ n))^p.toReal +
           (weightedStripSup SpectralWeight.one n (sourceResonantBMinusFunction hp ψ n))^p.toReal) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hcontrol,hroots⟩ := sourceLemma6_9 hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hr,_⟩ := hroots ψ hψ
  exact ⟨ξ,η,fun n hn => ⟨hr n hn,
    sourceGapProof_source_roots hp ψ n (ξ n) (η n) ((hcontrol n hn).2 ψ hψ) (hr n hn)⟩⟩

end NLS.ZakharovShabat
