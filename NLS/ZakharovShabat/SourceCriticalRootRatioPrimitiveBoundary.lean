import NLS.ComplexAnalysis.SquareRootPrimitiveBoundary
import NLS.ZakharovShabat.SourceCriticalRootRatioPrimitiveCommonBoundary
import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointPuncturedBound

/-!
# Full half-plane boundary values of quotient primitives

The selected-gap inverse-square-root bound upgrades matching vertical
ray limits to boundary limits for every approach inside each open
half-plane. The boundary values coincide at the two endpoints of an
open real-type gap, separately above and below the real axis.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any upper-half-plane primitive of the critical-root quotient has
one common full half-plane boundary value at both gap endpoints. -/
theorem sourceCriticalRootRatio_upperPrimitive_common_boundary_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im →
      HasDerivAt F
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z) z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ A : ℂ,
      Tendsto F (𝓝[{z : ℂ | 0 < z.im}] l) (𝓝 A) ∧
      Tendsto F (𝓝[{z : ℂ | 0 < z.im}] r) (𝓝 A) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  let δ : ℝ := (r.re-l.re)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨ε,M,hε,hM,hbound⟩ :=
    exists_sourceCriticalRootRatio_endpointPunctured_weighted_bound
      hp hp1 ψ hreal n hopen
  obtain ⟨A,hlray,hrray⟩ :=
    sourceCriticalRootRatio_upperPrimitive_common_vertical_limit
      hp hp1 ψ hreal n hopen F hF
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hweighted (c : ℂ) (hc : c ∈ ({l,r} : Set ℂ))
      (z : ℂ) (hz : 0 < z.im) (hpos : 0 < ‖z-c‖)
      (hsmall : ‖z-c‖ ≤ ε) :
      ‖f z * ((Real.sqrt (δ*‖z-c‖) : ℝ) : ℂ)‖ ≤ M := by
    have hdom : z ∈ sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal z (ne_of_gt hz)
    have hc' : c ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n} : Set ℂ) := hc
    have h := hbound c hc' z hdom
      (by simpa only [norm_sub_rev] using hpos)
      (by simpa only [norm_sub_rev] using hsmall)
    simpa only [f,δ,norm_sub_rev] using h
  refine ⟨A,?_,?_⟩
  · exact NLS.ComplexAnalysis.tendsto_primitive_upper_of_sqrt_bound
      f F l A δ M ε hl hδ hM.le hε hF
      (hweighted l (by change l = l ∨ l = r; exact Or.inl rfl)) hlray
  · exact NLS.ComplexAnalysis.tendsto_primitive_upper_of_sqrt_bound
      f F r A δ M ε hr hδ hM.le hε hF
      (hweighted r (by change r = l ∨ r = r; exact Or.inr rfl)) hrray

/-- Any lower-half-plane primitive of the critical-root quotient has
one common full half-plane boundary value at both gap endpoints. -/
theorem sourceCriticalRootRatio_lowerPrimitive_common_boundary_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, z.im < 0 →
      HasDerivAt F
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z) z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ A : ℂ,
      Tendsto F (𝓝[{z : ℂ | z.im < 0}] l) (𝓝 A) ∧
      Tendsto F (𝓝[{z : ℂ | z.im < 0}] r) (𝓝 A) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  let δ : ℝ := (r.re-l.re)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨ε,M,hε,hM,hbound⟩ :=
    exists_sourceCriticalRootRatio_endpointPunctured_weighted_bound
      hp hp1 ψ hreal n hopen
  obtain ⟨A,hlray,hrray⟩ :=
    sourceCriticalRootRatio_lowerPrimitive_common_vertical_limit
      hp hp1 ψ hreal n hopen F hF
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hweighted (c : ℂ) (hc : c ∈ ({l,r} : Set ℂ))
      (z : ℂ) (hz : z.im < 0) (hpos : 0 < ‖z-c‖)
      (hsmall : ‖z-c‖ ≤ ε) :
      ‖f z * ((Real.sqrt (δ*‖z-c‖) : ℝ) : ℂ)‖ ≤ M := by
    have hdom : z ∈ sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal z (ne_of_lt hz)
    have hc' : c ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n} : Set ℂ) := hc
    have h := hbound c hc' z hdom
      (by simpa only [norm_sub_rev] using hpos)
      (by simpa only [norm_sub_rev] using hsmall)
    simpa only [f,δ,norm_sub_rev] using h
  refine ⟨A,?_,?_⟩
  · exact NLS.ComplexAnalysis.tendsto_primitive_lower_of_sqrt_bound
      f F l A δ M ε hl hδ hM.le hε hF
      (hweighted l (by change l = l ∨ l = r; exact Or.inl rfl)) hlray
  · exact NLS.ComplexAnalysis.tendsto_primitive_lower_of_sqrt_bound
      f F r A δ M ε hr hδ hM.le hε hF
      (hweighted r (by change r = l ∨ r = r; exact Or.inr rfl)) hrray

end NLS.ZakharovShabat
