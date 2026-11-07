import NLS.Articles.KdVPseudomeasures.OriginalCompactSobolevLifts
import NLS.SequenceSpaces.PeriodOneMiuraFamilyRegularity
import NLS.KdV.PeriodOneOriginalSobolev

/-!
# A compact finite-p potential cover of the full original isospectral set

The continuous shifted Miura image of the compact stronger lift family is
inserted into the identical original period-two distribution space. The
compact image covers the entire original isospectral set and supplies one
uniform finite-p norm bound. Equality with the enlarged image is not needed.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.ZakharovShabat NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual original gaps of order -a yield a compact finite-p potential
cover at order -b, retaining every original isospectral member's entire
distribution. The strict quadratic-term threshold is b*p>1. -/
theorem exists_originalIsospectral_compact_finiteP_cover
    (q : OriginalHminusOnePotential) (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (a b : ℝ) (hab : a < b) (hb : b ≤ 1) (hbp : 1 < b*p.toReal)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev (-a) n:ℂ)*originalCanonicalGapValues q n) p) :
    ∃ K : Set (FourierLebesgueSpace (2:ℝ) (-b) p), IsCompact K ∧
      ∀ v ∈ originalIsospectralSet q, ∃ Q ∈ K, Q.val = v.val.val := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hb0 : 0 < b := by nlinarith only [hbp,hpR]
  obtain ⟨c,_,u₀,F,hF,hFc,_,hlift⟩ :=
    exists_originalIsospectral_compact_sobolev_lift_cover q hp hp2 a b hab hb hgap
  let L := hillMiuraRealSource ⁻¹' sourceIsospectralSet (by norm_num) (hillMiuraRealSource u₀)
  let : CompactSpace L := isCompact_iff_compactSpace.mp
    (isCompact_hillMiuraRealSource_isospectral_preimage u₀)
  let u : L → Coeff 2 := fun v => v.val.val
  have hu : Continuous u := continuous_subtype_val.comp continuous_subtype_val
  obtain ⟨G,hG,hGc⟩ := exists_continuous_periodOneMiura_finiteP_family hp b hbp u hu F hF hFc ((c:ℂ)^2)
  let Q := fun x => periodOneOriginalSobolev (-b) (by linarith only [hb0]) (G x)
  have hQ : Continuous Q := (periodOneOriginalSobolev (-b) _).continuous.comp hG
  refine ⟨range Q,isCompact_range hQ,fun v hv => ?_⟩
  obtain ⟨x,hx⟩ := hlift v hv
  refine ⟨Q x,mem_range_self x,?_⟩
  have he : periodOneMiura (u x)-periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)) =
      originalPeriodOneCoefficients v := by
    change periodOneMiura x.val.val-periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)) = _
    rw [hx]
    abel
  have hraw : (G x).val = (originalPeriodOneCoefficients v).val := by
    funext n
    rw [hGc,he]
  exact (periodOneOriginalSobolev_val (-b) _ (G x) (originalPeriodOneCoefficients v) hraw).trans
    (congrArg Subtype.val (periodOneOriginal_originalPeriodOneCoefficients v))

/-- A single finite-p norm bound for exact representatives of EVERY member
of the entire original H-minus-one isospectral set. -/
theorem exists_uniform_originalIsospectral_finiteP_bound
    (q : OriginalHminusOnePotential) (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (a b : ℝ) (hab : a < b) (hb : b ≤ 1) (hbp : 1 < b*p.toReal)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev (-a) n:ℂ)*originalCanonicalGapValues q n) p) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v ∈ originalIsospectralSet q,
      ∃ Q : FourierLebesgueSpace (2:ℝ) (-b) p, Q.val = v.val.val ∧ ‖Q‖ ≤ R := by
  obtain ⟨K,hK,hcover⟩ := exists_originalIsospectral_compact_finiteP_cover q hp hp2 a b hab hb hbp hgap
  obtain ⟨R,hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  refine ⟨max R 0,le_max_right _ _,fun v hv => ?_⟩
  obtain ⟨Q,hQ,hval⟩ := hcover v hv
  exact ⟨Q,hval,(hR Q hQ).trans (le_max_left _ _)⟩

end NLS.Articles.KdVPseudomeasures
