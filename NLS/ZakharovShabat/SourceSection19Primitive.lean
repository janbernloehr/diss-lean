import NLS.ZakharovShabat.SourceSection19Domain
import NLS.ZakharovShabat.SourceFullAbelianRealBoundary

/-!
# Lemma 19.1 and the literal original abelian integral

All assertions concern the same canonical primitive on the common source
neighborhood. A single relative-limit extension assigns the exact values at
every endpoint, while the filled square is analytic through its selected gap.
-/
noncomputable section
open Set Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One continuous endpoint extension, fixed before selecting the endpoint index. -/
def sourceAbelianEndpointExtension (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ) (ψ : CoeffPair p) : ℂ → ℂ :=
  denseLimitExtension (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
    (sourceCanonicalRootDomain hp hp1 ψ)

namespace SourceSection19Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W U : Set (CoeffPair p)}
variable (D : SourceSection19Data hp hp1 W U)
include D

/-- Lemma 19.1(i), with all collapsed gaps already filled. -/
theorem spectral_analytic (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) :
    AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
      (sourceOpenGapComplement hp hp1 ψ) := by
  obtain ⟨E⟩ := D.charts ψ hψ
  exact sourceFullAbelianPrimitive_spectral_analytic E n

/-- The original source gradient is equality of continuous-linear cotangents. -/
theorem source_derivative (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    HasFDerivAt (fun χ => sourceFullAbelianPrimitive hp hp1 W n (z,χ))
      ((sourceCanonicalRoot hp hp1 ψ z)⁻¹ • sourceDiscriminantCotangent hp z ψ) ψ :=
  D.toSourceFullAbelianDifferentialData.source_hasFDerivAt n z ψ hψ hz

/-- Lemma 19.1(ii), with the original additive normalization. -/
theorem index_shift (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceOpenGapComplement hp hp1 ψ) :
    sourceFullAbelianPrimitive hp hp1 W n (z,ψ) =
      sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ)+Complex.I*(Real.pi : ℂ)*n := by
  obtain ⟨E⟩ := D.charts ψ hψ
  exact sourceFullAbelianPrimitive_index_shift E n z hz

/-- Endpoint limits use the complete filled spectral domain, for every index. -/
theorem endpoint_limit (ψ : CoeffPair p) (hψ : ψ ∈ U) (j n : ℤ) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j} : Set ℂ)) :
    Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
      (𝓝[sourceOpenGapComplement hp hp1 ψ] a) (𝓝 (Complex.I*(Real.pi : ℂ)*(n-j))) := by
  obtain ⟨C,hC⟩ := D.cauchyFamily ψ hψ
  exact C.fullPrimitive_endpoint_limit_openGap j n ψ hC a ha

/-- Extending to endpoints leaves every original off-cut and filled value unchanged. -/
theorem endpointExtension_eqOn (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) :
    EqOn (sourceAbelianEndpointExtension hp hp1 W n ψ)
      (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)) (sourceOpenGapComplement hp hp1 ψ) := by
  obtain ⟨E⟩ := D.charts ψ hψ
  exact denseLimitExtension_eqOn_local _ _ _ _ (dense_sourceCanonicalRootDomain_complex hp hp1 ψ)
    (E.discs.isOpen_openGapComplement ψ E.source_mem) (D.spectral_analytic ψ hψ n).continuousOn (fun _ _ => rfl)

/-- The same extension is continuous at every endpoint and has the exact prescribed value. -/
theorem endpointExtension_value (ψ : CoeffPair p) (hψ : ψ ∈ U) (j n : ℤ) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j} : Set ℂ)) :
    sourceAbelianEndpointExtension hp hp1 W n ψ a = Complex.I*(Real.pi : ℂ)*(n-j) ∧
    ContinuousWithinAt (sourceAbelianEndpointExtension hp hp1 W n ψ)
      (insert a (sourceOpenGapComplement hp hp1 ψ)) a := by
  have hlim := D.endpoint_limit ψ hψ j n a ha
  have he : sourceAbelianEndpointExtension hp hp1 W n ψ a = Complex.I*(Real.pi : ℂ)*(n-j) :=
    denseLimitExtension_eq_of_tendsto _ _ (dense_sourceCanonicalRootDomain_complex hp hp1 ψ) _ _
      (hlim.mono_left (nhdsWithin_mono a (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ)))
  refine ⟨he,continuousWithinAt_insert_self.mpr ?_⟩
  change Tendsto _ _ (𝓝 (sourceAbelianEndpointExtension hp hp1 W n ψ a))
  rw [he]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (D.endpointExtension_eqOn ψ hψ n hz).symm

/-- Either literal endpoint integral and their original average compute this primitive. -/
theorem endpoint_integrals (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) (a ν : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAbelianEndpointIntegral hp hp1 ψ a ν = sourceFullAbelianPrimitive hp hp1 W n (ν,ψ) ∧
    sourceAbelianEndpointAverage hp hp1 n ν ψ = sourceFullAbelianPrimitive hp hp1 W n (ν,ψ) := by
  obtain ⟨C,hC⟩ := D.cauchyFamily ψ hψ
  exact ⟨C.endpointIntegral_eq ψ hC n a ν ha hν,C.endpointAverage_eq ψ hC n ν hν⟩

/-- The original integral is independent of every admissible interior C¹ path. -/
theorem endpointPath_integral (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) (a ν : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) (γ : Path a ν)
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) (hadm : SourceAdmissiblePath hp hp1 ψ γ) :
    Tendsto (fun t : ℝ × ℝ => truncatedPathIntegral (sourceAbelianDifferential hp hp1 ψ) γ t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ)))
      (𝓝 (sourceFullAbelianPrimitive hp hp1 W n (ν,ψ))) ∧
    improperPathIntegral (sourceAbelianDifferential hp hp1 ψ) γ = sourceFullAbelianPrimitive hp hp1 W n (ν,ψ) := by
  obtain ⟨C,hC⟩ := D.cauchyFamily ψ hψ
  exact C.endpointPath_integral ψ hC n a ν ha hν γ hγ hadm

/-- Piecewise C¹ admissible paths have the same actual improper value. -/
theorem endpointPiecewisePath_integral (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) (a ν : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) (Γ : PiecewiseInteriorC1Path a ν)
    (hadm : SourceAdmissiblePiecewisePath hp hp1 ψ Γ) :
    Tendsto (fun t : ℝ × ℝ => Γ.truncatedIntegral (sourceAbelianDifferential hp hp1 ψ) t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ)))
      (𝓝 (sourceFullAbelianPrimitive hp hp1 W n (ν,ψ))) ∧
    Γ.improperIntegral (sourceAbelianDifferential hp hp1 ψ) = sourceFullAbelianPrimitive hp hp1 W n (ν,ψ) := by
  obtain ⟨C,hC⟩ := D.cauchyFamily ψ hψ
  exact C.endpointPiecewisePath_integral ψ hC n a ν ha hν Γ hadm

/-- Lemma 19.1(iii) and Lemma 19.4 use one local family, with no tail cutoff. -/
theorem uniform_gap_bounds (φ : CoeffPair p) (hφ : φ ∈ U) :
    ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ U ∧
      V ⊆ ball C.discs.source.val C.discs.sourceRadius ∧ SourceAbelianMixedGapData C V ∧
      ∃ B : ℝ, 0 < B ∧ ∀ ψ ∈ V, ∀ n : ℤ, ∀ θ ∈ Icc (0 : ℝ) Real.pi, ∀ upper : Bool,
        ‖C.gapBoundary n ψ θ upper‖ ≤ B*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
  obtain ⟨C,V,hV,hφV,hVU,hVC,M⟩ := D.local_models φ hφ
  exact ⟨C,V,hV,hφV,hVU,hVC,M,M.uniform_boundary_bound⟩

/-- Lemma 19.1(iv) also admits a continuation through the selected gap. -/
theorem square_analytic (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) :
    AnalyticOnNhd ℂ (fun z => (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^2)
      (sourceOpenGapComplement hp hp1 ψ) ∧
    AnalyticOnNhd ℂ (fun z => sourceFullAbelianSquare hp hp1 W n (z,ψ))
      (sourceFullAbelianSquareDomain hp hp1 ψ n) := by
  obtain ⟨C,hC⟩ := D.cauchyFamily ψ hψ
  exact ⟨(D.spectral_analytic ψ hψ n).pow 2,C.fullSquare_analytic n ψ hC⟩

/-- Lemma 19.1(v), with arbitrary half-plane approach and the actual arcosh profile. -/
theorem real_gap_boundary (φ : realTypeSourceSubmodule p) (n : ℤ) (upper : Bool) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re) :
    Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val))
      (𝓝[sourceAbelianHalfPlane upper] (x:ℂ))
      (𝓝 (if upper then (sourceRealGapArcoshProfile hp φ.val n x : ℂ)
        else -(sourceRealGapArcoshProfile hp φ.val n x : ℂ))) := by
  obtain ⟨E⟩ := D.charts φ.val (D.real_subset φ.property)
  exact sourceFullAbelianPrimitive_real_gap_boundary_limit φ E n upper x hx

/-- Lemma 19.1(vi) and the exact zero-error clause of Lemma 19.4. -/
theorem zero (n : ℤ) (z : ℂ) :
    sourceFullAbelianPrimitive hp hp1 W n (z,0) = -Complex.I*z+Complex.I*(Real.pi:ℂ)*n ∧
    sourceFullAbelianPrimitive hp hp1 W n (z,0) = Complex.I*sourceStandardRoot hp hp1 (0 : CoeffPair p) n z := by
  obtain ⟨E⟩ := D.charts 0 (D.real_subset (by simp [realTypeSourceLocus]))
  exact ⟨sourceFullAbelianPrimitive_zero E n z,sourceFullAbelianPrimitive_zero_eq_I_mul_standardRoot E n z⟩

end SourceSection19Data
end NLS.ZakharovShabat
