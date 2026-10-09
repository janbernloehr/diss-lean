import NLS.ZakharovShabat.SourceLemmaF2

/-! # Corollary F.3: integrals between spectral endpoints

The integral is an iterated relative limit of actual polygonal curve integrals.
Its value is `i*pi*(n-m)` for either endpoint of gaps n and m, including
collapsed gaps. Consequently arbitrary pointwise choices of endpoints give
an analytic source functional, without regularity assumptions on the choices.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The second improper limit, at the terminal spectral endpoint. -/
def sourceAbelianEndpointToEndpointIntegral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (a b : ℂ) : ℂ :=
  limUnder (𝓝[sourceCanonicalRootDomain hp hp1 ψ] b)
    (fun ν => sourceAbelianEndpointIntegral hp hp1 ψ a ν)

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- The second endpoint limit exists and has the exact signed normalization. -/
theorem tendsto_endpointIntegral (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n m : ℤ) (a b : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hb : b ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ)) :
    Tendsto (fun ν => sourceAbelianEndpointIntegral hp hp1 ψ a ν)
      (𝓝[sourceCanonicalRootDomain hp hp1 ψ] b) (𝓝 (Complex.I*(Real.pi:ℂ)*(n-m))) := by
  have hlim := (C.fullPrimitive_endpoint_limit_openGap m n ψ hψ b hb).mono_left
    (nhdsWithin_mono b (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ν hν
  exact (C.endpointIntegral_eq ψ hψ n a ν ha hν).symm

/-- Either endpoint choice gives the same literal double improper integral. -/
theorem endpointToEndpointIntegral_eq (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n m : ℤ) (a b : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hb : b ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ)) :
    sourceAbelianEndpointToEndpointIntegral hp hp1 ψ a b = Complex.I*(Real.pi:ℂ)*(n-m) := by
  let : NeBot (𝓝[sourceCanonicalRootDomain hp hp1 ψ] b) :=
    mem_closure_iff_nhdsWithin_neBot.mp (C.endpoint_mem_closure_rootDomain ψ hψ m b hb)
  exact (C.tendsto_endpointIntegral ψ hψ n m a b ha hb).limUnder_eq

/-- Every integrable admissible C1 path has the double improper integral's value. -/
theorem endpointToEndpointCurveIntegral_eq (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n m : ℤ) (a b : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hb : b ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ))
    (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hpath : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hint : CurveIntegrable (holomorphicOneForm (sourceAbelianDifferential hp hp1 ψ)) γ) :
    (∫ᶜ z in γ, holomorphicOneForm (sourceAbelianDifferential hp hp1 ψ) z) =
      sourceAbelianEndpointToEndpointIntegral hp hp1 ψ a b := by
  obtain ⟨E⟩ := C.charts ψ hψ
  rw [C.endpointToEndpointIntegral_eq ψ hψ n m a b ha hb]
  have haLim := (C.fullPrimitive_endpoint_limit_openGap n n ψ hψ a ha).mono_left
    (nhdsWithin_mono a (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ))
  have hbLim := (C.fullPrimitive_endpoint_limit_openGap m n ψ hψ b hb).mono_left
    (nhdsWithin_mono b (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ))
  simp only [sub_self,mul_zero] at haLim
  simpa only [sub_zero] using curveIntegral_eq_sub_of_primitive_boundary_ends
    (sourceAbelianDifferential hp hp1 ψ) (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
    (sourceCanonicalRootDomain hp hp1 ψ)
    (fun z hz => sourceFullAbelianPrimitive_hasDerivAt E n z hz) γ hγ hpath hint haLim hbLim

/-- Pointwise endpoint choices suffice: neither choice is required to be continuous. -/
theorem endpointToEndpointIntegral_analytic (n m : ℤ) (a b : CoeffPair p → ℂ)
    (ha : ∀ ψ ∈ ball C.discs.source.val C.discs.sourceRadius,
      a ψ ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hb : ∀ ψ ∈ ball C.discs.source.val C.discs.sourceRadius,
      b ψ ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ)) :
    AnalyticOnNhd ℂ (fun ψ => sourceAbelianEndpointToEndpointIntegral hp hp1 ψ (a ψ) (b ψ))
      (ball C.discs.source.val C.discs.sourceRadius) := by
  intro ψ hψ
  apply (analyticAt_const (v := Complex.I*(Real.pi:ℂ)*(n-m))).congr
  filter_upwards [isOpen_ball.mem_nhds hψ] with χ hχ
  exact (C.endpointToEndpointIntegral_eq χ hχ n m (a χ) (b χ) (ha χ hχ) (hb χ hχ)).symm

end SourceFullAbelianUniformCauchyFamily

/-- F.3 on one connected almost-real domain, simultaneously for all signed gaps
and every pointwise selection of their endpoints. The exact value also shows
independence of the choices, vanishing for n=m, and antisymmetry. -/
theorem sourceCorollaryF3 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ realTypeSourceLocus p ⊆ V ∧
      ∀ n m : ℤ, ∀ a b : CoeffPair p → ℂ,
        (∀ ψ ∈ V, a ψ ∈
          ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
            canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) →
        (∀ ψ ∈ V, b ψ ∈
          ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
            canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ)) →
        AnalyticOnNhd ℂ (fun ψ => sourceAbelianEndpointToEndpointIntegral hp hp1 ψ (a ψ) (b ψ)) V ∧
        ∀ ψ ∈ V, sourceAbelianEndpointToEndpointIntegral hp hp1 ψ (a ψ) (b ψ) =
          Complex.I*(Real.pi:ℂ)*(n-m) := by
  obtain ⟨W,V,hV,hconn,hr,_,hlocal⟩ := sourceLemmaF2 hp hp1
  refine ⟨V,hV,hconn,hr,?_⟩
  intro n m a b ha hb
  have heq : ∀ ψ ∈ V, sourceAbelianEndpointToEndpointIntegral hp hp1 ψ (a ψ) (b ψ) =
      Complex.I*(Real.pi:ℂ)*(n-m) := by
    intro ψ hψ
    obtain ⟨C,r,hr,_,hsub,_⟩ := hlocal ψ hψ
    exact C.endpointToEndpointIntegral_eq ψ (hsub (mem_ball_self hr)) n m (a ψ) (b ψ)
      (ha ψ hψ) (hb ψ hψ)
  refine ⟨?_,heq⟩
  intro ψ hψ
  apply (analyticAt_const (v := Complex.I*(Real.pi:ℂ)*(n-m))).congr
  filter_upwards [hV.mem_nhds hψ] with χ hχ
  exact (heq χ hχ).symm

/-- At the free source all gaps collapse, but the signed integral remains exact. -/
theorem sourceAbelianEndpointToEndpointIntegral_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) :
    sourceAbelianEndpointToEndpointIntegral hp hp1 (0 : CoeffPair p)
      ((Real.pi:ℂ)*n) ((Real.pi:ℂ)*m) = Complex.I*(Real.pi:ℂ)*(n-m) := by
  obtain ⟨W,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hC⟩ := hfamilies (0 : realTypeSourceSubmodule p)
  have h0 : (0 : CoeffPair p) ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  apply C.endpointToEndpointIntegral_eq 0 h0 n m <;>
    simp [map_zero,canonicalPeriodicLeft_zero,canonicalPeriodicRight_zero]

end NLS.ZakharovShabat
