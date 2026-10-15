import NLS.ZakharovShabat.SourcePsiExteriorNormalization
import NLS.ZakharovShabat.SourcePsiDoubleOmittedProduct
import NLS.ZakharovShabat.SourcePsiDeletedRootFill

/-!
# The literal outer-circle product in Lemma 12.11

Inserting the omitted factor gives the unconditional product over all
standard roots, including numerator collisions. This literal product
agrees with the exterior ratio and tends uniformly to one on large
half-integer circles. Filling the omitted root with the moving midpoint
gives the source's pole formula everywhere off the spectral gaps.
Both individual product/sine ratios tend to minus one, correcting the
printed signs; their quotient and the diagonal normalization are unchanged.
-/

noncomputable section
open Set Complex Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Inserting the omitted factor identifies the literal full standard-root quotient. -/
theorem sourcePsiFullRatio_hasProd (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    HasProd (fun m : ℤ => (displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z)
      ((displacedRoots a n-z)*sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))/I) := by
  let f (m : ℤ) := (displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z
  let Q := sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))
  have hprod : HasProd (fun m : {m : ℤ // m ≠ n} => f m) Q :=
    hasProd_sourceSingleRootQuotient_subtype hp hp1 ψ a z n (fun m _ => hz m)
  have hcompl : HasProd (({n}:Set ℤ)ᶜ.domRestrict f) Q := hprod
  have hall : HasProd f (f n*Q) := (hasProd_singleton n f).mul_compl hcompl
  have hn := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hz n)
  have ho := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n (fun m _ => hz m)
  have hratio : sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)) =
      I*Q/sourceStandardRoot hp hp1 ψ n z := by
    unfold sourcePsiContourIntegrandJoint sourcePsiCandidate Q sourceSingleRootQuotientJointProduct
      sourceStandardRootOmittedJointProduct
    rw [sourceCanonicalRoot_eq_omitted hp hp1 n ψ z]
    field_simp [hn,ho,Complex.I_ne_zero]
    simp [Complex.I_sq]
  have he : f n*Q = (displacedRoots a n-z)*sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))/I := by
    rw [hratio]
    dsimp only [f]
    field_simp
  exact he ▸ hall

/-- The full product is the exterior ratio on the gap and free-lattice complement. -/
theorem sourcePsiFullRatio_eq_exterior (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) (hzfree : z ∉ freeLattice) :
    (∏' m : ℤ, (displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z) =
      sourcePsiExteriorProductRatio hp hp1 a ψ z := by
  rw [(sourcePsiFullRatio_hasProd hp hp1 n a ψ z hz).tprod_eq]
  exact sourcePsiContourIntegrand_relative_pole_eq hp hp1 n a ψ z hzfree

/-- The literal product in the source tends uniformly to one on all large outer circles. -/
theorem eventually_centralCircle_sourcePsiFullRatio_close
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (ψ : CoeffPair p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖(∏' m : ℤ, (displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z)-1‖ ≤ ε := by
  filter_upwards [eventually_centralCircle_sourceCanonicalRootDomain hp hp1 ψ,
    eventually_centralCircle_sourcePsiExteriorProductRatio_close hp hp1 a ψ hε] with k hk hb z hz
  rw [sourcePsiFullRatio_eq_exterior hp hp1 0 a ψ z (hk hz)
    (notMem_freeLattice_of_separated (by positivity : 0 < Real.pi/2)
      (fun m => centralCircle_lattice_gap k hz m))]
  exact hb z hz

/-- Filling the unused root by the moving midpoint gives the source's literal pole formula. -/
theorem sourcePsiContourIntegrand_midpoint_fullProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (b : DeletedCoeff p n)
    (ψ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourcePsiContourIntegrandJoint hp hp1 n (z,((b:Coeff p),ψ)) =
      I/(sourceStandardRootMidpoint hp hp1 ψ n-z)*
        ∏' m : ℤ, (displacedRoots (sourcePsiFillDeletedRoot n b (sourceStandardRootMidpoint hp hp1 ψ n)) m-z)/
          sourceStandardRoot hp hp1 ψ m z := by
  let a := sourcePsiFillDeletedRoot n b (sourceStandardRootMidpoint hp hp1 ψ n)
  have hfill : sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)) =
      sourcePsiContourIntegrandJoint hp hp1 n (z,((b:Coeff p),ψ)) := by
    unfold sourcePsiContourIntegrandJoint
    congr 1
    apply sourcePsiCandidate_eq_of_off_index hp hp1 n z
    intro m hm
    exact sourcePsiFillDeletedRoot_apply_other n m hm b _
  have hn : sourceStandardRootMidpoint hp hp1 ψ n-z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    exact hz n (heq ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  rw [(sourcePsiFullRatio_hasProd hp hp1 n a ψ z hz).tprod_eq,
    displacedRoots_sourcePsiFillDeletedRoot_same,hfill]
  field_simp

/-- The numerator's individual sine asymptotic has sign minus with π₀=1. -/
theorem eventually_centralCircle_sourcePsiNumerator_sine_sign
    (hp : p ≠ ⊤) (a : Coeff p) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖(entireSingleSpectralProduct (displacedRoots a) z/2)/sin z+1‖ ≤ ε := by
  obtain ⟨K,hK⟩ := eventually_centralCircle_entireSingleSpectralProduct_div_free_close
    hp (displacedRoots a) (memℓp_displacedRoots a) hε
  refine ⟨K,?_⟩
  intro k hk z hz
  have he : (entireSingleSpectralProduct (displacedRoots a) z/2)/sin z+1 =
      -(entireSingleSpectralProduct (displacedRoots a) z/(-2*sin z)-1) := by
    simp only [div_div,neg_mul,div_neg]
    ring
  rw [he,norm_neg]
  exact hK k hk z hz

/-- The standard-root product has the same negative sine asymptotic. -/
theorem eventually_centralCircle_sourceStandardProduct_sine_sign
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖(sourceCanonicalRoot hp hp1 ψ z/(2*I))/sin z+1‖ ≤ ε := by
  obtain ⟨K,hK⟩ := eventually_centralCircle_sourceCanonicalRoot_div_free_close hp hp1 ψ hε
  refine ⟨K,?_⟩
  intro k hk z hz
  have he : (sourceCanonicalRoot hp hp1 ψ z/(2*I))/sin z+1 =
      -(sourceCanonicalRoot hp hp1 ψ z/(-2*I*sin z)-1) := by
    simp only [div_div,neg_mul,div_neg]
    ring
  rw [he,norm_neg]
  exact hK k hk z hz

/-- At the free source both individual products are exactly minus sine. -/
theorem sourcePsi_free_product_sineSigns (hp : p ≠ ⊤) (hp1 : 1 < p) (z : ℂ) :
    entireSingleSpectralProduct (displacedRoots (0:Coeff p)) z/2 = -sin z ∧
      sourceCanonicalRoot hp hp1 (0:CoeffPair p) z/(2*I) = -sin z := by
  have hzero : displacedRoots (0:Coeff p) = fun m : ℤ => (Real.pi:ℂ)*m := by
    funext m
    simp [displacedRoots]
  rw [hzero,entireSingleSpectralProduct_free,sourceCanonicalRoot_zero_source_eq_free_sine hp hp1 0]
  constructor <;> field_simp

/-- The printed positive-sine normalization has error two on every free outer circle. -/
theorem sourcePsi_free_positiveSine_error (hp : p ≠ ⊤) (hp1 : 1 < p)
    (k : ℕ) (z : ℂ) (hz : z ∈ sphere (0:ℂ) (centralCircleRadius k)) :
    ‖(entireSingleSpectralProduct (displacedRoots (0:Coeff p)) z/2)/sin z-1‖ = 2 ∧
      ‖(sourceCanonicalRoot hp hp1 (0:CoeffPair p) z/(2*I))/sin z-1‖ = 2 := by
  have hs : sin z ≠ 0 := sin_ne_zero_of_notMem_freeLattice
    (notMem_freeLattice_of_separated (by positivity : 0 < Real.pi/2)
      (fun m => centralCircle_lattice_gap k hz m))
  obtain ⟨hn,hd⟩ := sourcePsi_free_product_sineSigns hp hp1 z
  rw [hn,hd]
  norm_num [neg_div,div_self hs]

end NLS.ZakharovShabat
