import NLS.ZakharovShabat.SourcePeriodicEndpointContinuity
import NLS.ZakharovShabat.SourceCriticalDisplacementContinuity
import NLS.ZakharovShabat.SourceSegmentIndexSeparation
import NLS.ZakharovShabat.SourceCriticalRootRatioOuterArcs

/-! # Uniform adjacent distance comparisons near real sources

Uniform continuity of the actual spectral sequences preserves strict
real gap separation. One neighborhood works for all signed indices and
all points of every complex periodic gap.
-/
noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform continuity of the actual critical points, over all indices. -/
theorem section28_uniform_critical_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ ∀ ψ ∈ U, ∀ n : ℤ,
      ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n‖ < ε := by
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp
    (continuousAt_sourceCriticalDisplacement_of_realType hp hp1 φ hφ) ε hε
  refine ⟨ball φ δ,isOpen_ball,mem_ball_self hδ,?_⟩
  intro ψ hψ n
  have hb := hd hψ
  rw [dist_eq_norm] at hb
  have he := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
    (sourceCriticalDisplacement hp hp1 ψ-sourceCriticalDisplacement hp hp1 φ) n).trans_lt hb
  simpa only [lp.coeFn_sub,Pi.sub_apply,sourceCriticalDisplacement,
    canonicalCriticalDisplacement_apply,sub_sub_sub_cancel_right] using he

/-- Endpoint perturbations control every point on the whole moving segment. -/
theorem section28_segment_near_segment (l r l₀ r₀ : ℂ) (ε : ℝ)
    (hl : ‖l-l₀‖ ≤ ε) (hr : ‖r-r₀‖ ≤ ε)
    (z : ℂ) (hz : z ∈ segment ℝ l r) :
    ∃ z₀ ∈ segment ℝ l₀ r₀, ‖z-z₀‖ ≤ ε := by
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hz
  refine ⟨a • l₀+b • r₀,⟨a,b,ha,hb,hab,rfl⟩,?_⟩
  have he : a • l+b • r-(a • l₀+b • r₀) = a • (l-l₀)+b • (r-r₀) := by module
  rw [he]
  calc
    ‖a • (l-l₀)+b • (r-r₀)‖ ≤ ‖a • (l-l₀)‖+‖b • (r-r₀)‖ := norm_add_le _ _
    _ = a*‖l-l₀‖+b*‖r-r₀‖ := by rw [norm_smul,norm_smul,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb]
    _ ≤ a*ε+b*ε := add_le_add (mul_le_mul_of_nonneg_left hl ha) (mul_le_mul_of_nonneg_left hr hb)
    _ = ε := by rw [← add_mul,hab,one_mul]

/-- A strict real distance margin survives three simultaneous perturbations. -/
theorem section28_distance_lt_of_real_margin (a b z : ℂ) (a₀ b₀ z₀ ε : ℝ)
    (hab : 4*ε < b₀-a₀) (hbz : b₀ ≤ z₀)
    (ha : ‖a-(a₀:ℂ)‖ ≤ ε) (hb : ‖b-(b₀:ℂ)‖ ≤ ε)
    (hz : ‖z-(z₀:ℂ)‖ ≤ ε) : ‖b-z‖ < ‖a-z‖ := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans ha
  have haz : a₀ ≤ z₀ := by linarith
  have hnorm (x : ℝ) (hx : x ≤ z₀) : ‖(x:ℂ)-(z₀:ℂ)‖ = z₀-x := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hx)]
    ring
  have hb' : ‖b-z‖ ≤ ε+(z₀-b₀)+ε := by
    calc
      ‖b-z‖ = ‖(b-(b₀:ℂ))+((b₀:ℂ)-(z₀:ℂ))+((z₀:ℂ)-z)‖ := by congr 1; ring
      _ ≤ ‖b-(b₀:ℂ)‖+‖(b₀:ℂ)-(z₀:ℂ)‖+‖(z₀:ℂ)-z‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ε+(z₀-b₀)+ε := by rw [hnorm b₀ hbz,norm_sub_rev (z₀:ℂ) z]; linarith
  have ha' : z₀-a₀ ≤ ε+‖a-z‖+ε := by
    calc
      z₀-a₀ = ‖(a₀:ℂ)-(z₀:ℂ)‖ := (hnorm a₀ haz).symm
      _ = ‖((a₀:ℂ)-a)+(a-z)+(z-(z₀:ℂ))‖ := by congr 1; ring
      _ ≤ ‖(a₀:ℂ)-a‖+‖a-z‖+‖z-(z₀:ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ε+‖a-z‖+ε := by rw [norm_sub_rev (a₀:ℂ) a]; linarith
  linarith

/-- Real neighboring endpoint gaps have a positive uniform margin. -/
theorem section28_real_uniform_gap_margin (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ,
      δ ≤ (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m).re-
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (m-1)).re := by
  obtain ⟨V,_,_,hφV,C,hC,hsep⟩ := exists_local_source_segment_index_separation hp hp1 φ hφ
  have hCpos : 0 < C := by linarith
  refine ⟨1/C,by positivity,?_⟩
  intro m
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (m-1)
  have hreal := isRealType_periodOnePotential φ hφ
  have hl : (l.re:ℂ) = l := Complex.ext (by simp) (by
    simpa only [Complex.ofReal_im] using (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ _ hreal m).1.symm)
  have hr : (r.re:ℂ) = r := Complex.ext (by simp) (by
    simpa only [Complex.ofReal_im] using (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ _ hreal (m-1)).2.symm)
  have hrl : r.re < l.re := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _ _ hreal (by omega)
  have hs := hsep φ hφV (m-1) m (by omega) r (right_mem_segment ℝ _ _) l (left_mem_segment ℝ _ _)
  have hn : ‖l-r‖ = l.re-r.re := by
    calc
      ‖l-r‖ = ‖((l.re-r.re:ℝ):ℂ)‖ := by rw [Complex.ofReal_sub,hl,hr]
      _ = l.re-r.re := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hrl)]
  norm_num only [sub_sub_cancel_left,Int.cast_neg,Int.cast_one,abs_neg,abs_one] at hs
  rw [hn] at hs
  exact (div_le_iff₀ hCpos).mpr (by nlinarith)

/-- The same perturbation comparison on the left side of the real axis. -/
theorem section28_distance_lt_of_real_margin_left (a b z : ℂ) (a₀ b₀ z₀ ε : ℝ)
    (hab : 4*ε < a₀-b₀) (hbz : z₀ ≤ b₀)
    (ha : ‖a-(a₀:ℂ)‖ ≤ ε) (hb : ‖b-(b₀:ℂ)‖ ≤ ε)
    (hz : ‖z-(z₀:ℂ)‖ ≤ ε) : ‖b-z‖ < ‖a-z‖ := by
  have h := section28_distance_lt_of_real_margin (-a) (-b) (-z)
    (-a₀) (-b₀) (-z₀) ε (by linarith) (by linarith)
    (by simpa only [Complex.ofReal_neg,neg_sub_neg,norm_sub_rev] using ha)
    (by simpa only [Complex.ofReal_neg,neg_sub_neg,norm_sub_rev] using hb)
    (by simpa only [Complex.ofReal_neg,neg_sub_neg,norm_sub_rev] using hz)
  simpa only [neg_sub_neg,norm_sub_rev] using h

/-- The actual adjacent distance inequalities hold for every signed index
on one complex neighborhood of any real source. -/
theorem section28_local_adjacent_distance (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ ∀ ψ ∈ U, ∀ m n : ℤ,
      ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n,
        (m < n →
          ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ <
            ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (m-1)-z‖ ∧
          ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ <
            ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (m-1)-z‖) ∧
        (n < m →
          ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ <
            ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (m+1)-z‖ ∧
          ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ <
            ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (m+1)-z‖) := by
  obtain ⟨δ,hδ,hmargin⟩ := section28_real_uniform_gap_margin hp hp1 φ hφ
  obtain ⟨E,hE,hφE,hend⟩ := exists_uniform_sourcePeriodicEndpoint_neighborhood hp hp1 φ hφ
    (by positivity : 0 < δ/8)
  obtain ⟨C,hC,hφC,hcrit⟩ := section28_uniform_critical_neighborhood hp hp1 φ hφ
    (by positivity : 0 < δ/8)
  refine ⟨E ∩ C,hE.inter hC,⟨hφE,hφC⟩,?_⟩
  intro ψ hψ m n z hz
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  let c := canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  have hreal := isRealType_periodOnePotential φ hφ
  have real_eq (x : ℂ) (hx : x.im = 0) : (x.re:ℂ) = x :=
    Complex.ext (by simp) (by simpa using hx.symm)
  have hl (j : ℤ) : ((l j).re:ℂ) = l j := real_eq _
    (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ _ hreal j).1
  have hr (j : ℤ) : ((r j).re:ℂ) = r j := real_eq _
    (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ _ hreal j).2
  have hc (j : ℤ) : ((c j).re:ℂ) = c j := real_eq _
    (canonicalCriticalPoints_im_eq_zero hp hp1 _ _ hreal j)
  obtain ⟨z₀,hz₀,hzz₀⟩ := section28_segment_near_segment _ _ (l n) (r n) (δ/8)
    (hend ψ hψ.1 n).1.le (hend ψ hψ.1 n).2.le z hz
  have hz₀re := sourcePeriodicSegment_re_mem_Icc hp hp1 φ n z₀ hz₀
  have hz₀eq := real_eq z₀ (sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ hφ n z₀ hz₀)
  have hcseg := canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) hreal m
  have hcclose : ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-
      ((c m).re:ℂ)‖ ≤ δ/8 := by rw [hc]; exact (hcrit ψ hψ.2 m).le
  have hzclose : ‖z-(z₀.re:ℂ)‖ ≤ δ/8 := by rw [hz₀eq]; exact hzz₀
  have hlr (j : ℤ) : (l j).re ≤ (r j).re :=
    re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 _ _).2.1 j)
  constructor
  · intro hmn
    have hmz : (c m).re ≤ z₀.re := hcseg.2.trans
      ((canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _ _ hreal hmn).le.trans hz₀re.1)
    have hgap : δ ≤ (c m).re-(r (m-1)).re := by
      have h := hmargin m
      change δ ≤ (l m).re-(r (m-1)).re at h
      change (l m).re ≤ (c m).re ∧ (c m).re ≤ (r m).re at hcseg
      linarith
    constructor
    · apply section28_distance_lt_of_real_margin _ _ z (l (m-1)).re (c m).re z₀.re (δ/8)
        (by linarith [hlr (m-1)]) hmz ?_ hcclose hzclose
      rw [hl]; exact (hend ψ hψ.1 (m-1)).1.le
    · apply section28_distance_lt_of_real_margin _ _ z (r (m-1)).re (c m).re z₀.re (δ/8)
        (by linarith) hmz ?_ hcclose hzclose
      rw [hr]; exact (hend ψ hψ.1 (m-1)).2.le
  · intro hnm
    have hzm : z₀.re ≤ (c m).re := hz₀re.2.trans
      ((canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _ _ hreal hnm).le.trans hcseg.1)
    have hgap : δ ≤ (l (m+1)).re-(c m).re := by
      have h := hmargin (m+1)
      have he : m+1-1 = m := by omega
      rw [he] at h
      change δ ≤ (l (m+1)).re-(r m).re at h
      change (l m).re ≤ (c m).re ∧ (c m).re ≤ (r m).re at hcseg
      linarith
    constructor
    · apply section28_distance_lt_of_real_margin_left _ _ z (l (m+1)).re (c m).re z₀.re (δ/8)
        (by linarith) hzm ?_ hcclose hzclose
      rw [hl]; exact (hend ψ hψ.1 (m+1)).1.le
    · apply section28_distance_lt_of_real_margin_left _ _ z (r (m+1)).re (c m).re z₀.re (δ/8)
        (by linarith [hlr (m+1)]) hzm ?_ hcclose hzclose
      rw [hr]; exact (hend ψ hψ.1 (m+1)).2.le

/-- The two signed distance comparisons share a connected open neighborhood
of the whole real locus, inside any prescribed open source domain. -/
theorem section28_adjacent_distance_neighborhood_within (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hrealW : realTypeSourceLocus p ⊆ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ W ∧
      ∀ ψ ∈ U, ∀ m n : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n,
        (m < n →
          ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ <
            ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (m-1)-z‖ ∧
          ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ <
            ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (m-1)-z‖) ∧
        (n < m →
          ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ <
            ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (m+1)-z‖ ∧
          ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ <
            ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (m+1)-z‖) := by
  classical
  let R := {φ : CoeffPair p // IsRealType (CoeffPair.toMax p φ)}
  have hlocal (φ : R) := section28_local_adjacent_distance hp hp1 φ.val φ.property
  choose V hV hφV hbound using hlocal
  let S := (⋃ φ : R, V φ) ∩ W
  have hS : IsOpen S := (isOpen_iUnion hV).inter hW
  have hrS : realTypeSourceLocus p ⊆ S := fun φ hφ =>
    ⟨mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφV ⟨φ,hφ⟩⟩,hrealW hφ⟩
  have hz : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  refine ⟨U,hS.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr (hrS hz),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hz hrS,
    fun ψ hψ => (hUS hψ).2,?_⟩
  intro ψ hψ m n z hz
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ).1
  exact hbound φ ψ hφ m n z hz

end NLS.ZakharovShabat
