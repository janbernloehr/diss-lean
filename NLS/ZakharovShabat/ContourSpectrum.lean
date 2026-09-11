import NLS.ZakharovShabat.ContourProjection
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Identification of contour and algebraic spectral projections

The finite-dimensional range of a contour projection decomposes into generalized
eigenspaces of a restricted resolvent. The contour selection law identifies this
range with the sum of the enclosed periodic root spaces, proving operator equality
and the algebraic-multiplicity formula for its rank.
-/

open scoped ENNReal
open Complex Metric Set Classical
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite set of periodic spectral values inside a disk. -/
def enclosedPeriodicSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) : Finset ℂ :=
  (finite_periodicSpectrum_inter_of_isBounded hp φ (K := ball c r) isBounded_ball).toFinset

@[simp] theorem mem_enclosedPeriodicSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (c z : ℂ) (r : ℝ) :
    z ∈ enclosedPeriodicSpectrum hp φ c r ↔ z ∈ periodicSpectrum hp φ ∧ z ∈ ball c r :=
  Set.Finite.mem_toFinset _

/-- The contour range contains no vectors beyond the enclosed full root spaces. -/
theorem range_resolventCircleIntegral_le_cluster (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    (resolventCircleIntegral hp φ c r).range ≤
      periodicClusterSpace hp φ (enclosedPeriodicSpectrum hp φ c r) := by
  let P := resolventCircleIntegral hp φ c r
  let V := P.range
  let G := periodicClusterSpace hp φ (enclosedPeriodicSpectrum hp φ c r)
  let : FiniteDimensional ℂ V := finiteDimensional_range_resolventCircleIntegral hp φ c r hr hc
  obtain ⟨w, hw⟩ := resolventSet_nonempty hp φ
  let R := resolvent hp φ w
  have hRinj : Function.Injective R := by
    intro x y h
    apply Function.LeftInverse.injective (spectralPencil_resolventToDomain hp φ w hw)
    exact domainInclusion_injective h
  have hcomm : Commute P R := resolventCircleIntegral_commute_resolvent hp φ c w r hr hc hw
  have hV : ∀ x : PairSpace p, x ∈ V → R.toLinearMap x ∈ V := by
    rintro x ⟨y, rfl⟩
    exact ⟨R y, DFunLike.congr_fun hcomm.eq y⟩
  let A := R.toLinearMap.restrict hV
  have hfix (x : V) : P x = x := by
    obtain ⟨y, hy⟩ := x.property
    calc
      P x = P (P y) := congrArg P hy.symm
      _ = P y := DFunLike.congr_fun (resolventCircleIntegral_idempotent hp φ c r hr hc) y
      _ = x := hy
  have hle : (⊤ : Submodule ℂ V) ≤ G.comap V.subtype := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top A]
    apply iSup_le
    intro μ x hx
    change (x : PairSpace p) ∈ G
    have hxR : (x : PairSpace p) ∈ Module.End.genEigenspace R.toLinearMap μ ⊤ := by
      change x ∈ Module.End.genEigenspace (R.toLinearMap.restrict hV) μ ⊤ at hx
      rw [Module.End.genEigenspace_restrict] at hx
      exact hx
    by_cases hμ : μ = 0
    · subst μ
      obtain ⟨n, hn⟩ := Module.End.mem_genEigenspace_top.mp hxR
      simp only [zero_smul, sub_zero, LinearMap.mem_ker] at hn
      have hinj : Function.Injective (R.toLinearMap ^ n) := by
        simpa only [Module.End.coe_pow, ContinuousLinearMap.coe_coe] using hRinj.iterate n
      have hx0 : (x : PairSpace p) = 0 := hinj (hn.trans (map_zero _).symm)
      rw [hx0]
      exact G.zero_mem
    · let z := w - μ⁻¹
      have hzw : z ≠ w := by simp [z, sub_eq_self, hμ]
      have hμz : (w - z)⁻¹ = μ := by simp [z]
      have hxroot : (x : PairSpace p) ∈ periodicRootSpaceTop hp φ z := by
        rw [periodicRootSpaceTop_eq_resolvent_genEigenspace hp φ w z hw hzw, hμz]
        exact hxR
      by_cases hzspec : z ∈ periodicSpectrum hp φ
      · by_cases hzin : z ∈ ball c r
        · have hzset := (mem_enclosedPeriodicSpectrum hp φ c z r).mpr ⟨hzspec, hzin⟩
          have hroot : periodicRootSpaceTop hp φ z ≤ G :=
            le_iSup_of_le z (le_iSup_of_le hzset le_rfl)
          exact hroot hxroot
        · have hzero := resolventCircleIntegral_mul_projection_eq_ite hp φ c z r hr hc
          rw [if_neg hzin] at hzero
          have hxzero := DFunLike.congr_fun hzero (x : PairSpace p)
          change P (periodicSpectralProjection hp φ z x) = 0 at hxzero
          rw [periodicSpectralProjection_apply_root hp φ z x hxroot, hfix] at hxzero
          rw [hxzero]
          exact G.zero_mem
      · have hzres : z ∈ resolventSet hp φ := Classical.not_not.mp hzspec
        rw [periodicRootSpaceTop_eq_bot_of_mem_resolventSet hp φ z hzres] at hxroot
        have hxzero : (x : PairSpace p) = 0 := hxroot
        rw [hxzero]
        exact G.zero_mem
  intro x hx
  exact hle (show (⟨x, hx⟩ : V) ∈ (⊤ : Submodule ℂ V) from Submodule.mem_top)

/-- The contour range is exactly the sum of the enclosed full periodic root spaces. -/
theorem range_resolventCircleIntegral (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    (resolventCircleIntegral hp φ c r).range =
      periodicClusterSpace hp φ (enclosedPeriodicSpectrum hp φ c r) := by
  apply le_antisymm (range_resolventCircleIntegral_le_cluster hp φ c r hr hc)
  apply iSup_le
  intro z
  apply iSup_le
  intro hz x hx
  exact ⟨x, resolventCircleIntegral_apply_root hp φ c z r hc
    ((mem_enclosedPeriodicSpectrum hp φ c z r).mp hz).2 x hx⟩

/-- The operator-norm contour integral equals the algebraically constructed
projection onto its enclosed finite spectral cluster. -/
theorem resolventCircleIntegral_eq_clusterProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    resolventCircleIntegral hp φ c r =
      periodicClusterProjection hp φ (enclosedPeriodicSpectrum hp φ c r) := by
  let P := resolventCircleIntegral hp φ c r
  let s := enclosedPeriodicSpectrum hp φ c r
  let Q := periodicClusterProjection hp φ s
  have hPQ : P * Q = Q := by
    have h := resolventCircleIntegral_mul_cluster hp φ c r hr hc s
    have hs : s.filter (fun z => z ∈ ball c r) = s := by
      apply Finset.filter_eq_self.mpr
      intro z hz
      exact ((mem_enclosedPeriodicSpectrum hp φ c z r).mp hz).2
    rw [hs] at h
    exact h
  have hcomm : Commute Q P := by
    exact Commute.sum_left s _ _ fun z _ => periodicSpectralProjection_commute_contour hp φ c z r hr hc
  have hQP : Q * P = P := by
    apply ContinuousLinearMap.ext
    intro x
    have hx : P x ∈ Q.range := by
      rw [range_periodicClusterProjection, ← range_resolventCircleIntegral hp φ c r hr hc]
      exact LinearMap.mem_range_self _ x
    obtain ⟨y, hy⟩ := hx
    change Q (P x) = P x
    rw [← hy]
    exact DFunLike.congr_fun (periodicClusterProjection_idempotent hp φ s) y
  exact hQP.symm.trans (hcomm.eq.trans hPQ)

/-- The rank of a Cauchy–Riesz circle projection counts enclosed algebraic multiplicities. -/
theorem finrank_range_resolventCircleIntegral (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    Module.finrank ℂ (resolventCircleIntegral hp φ c r).range =
      ∑ z ∈ enclosedPeriodicSpectrum hp φ c r, periodicAlgebraicMultiplicity hp φ z := by
  rw [resolventCircleIntegral_eq_clusterProjection hp φ c r hr hc]
  exact finrank_range_periodicClusterProjection hp φ _

/-- The contour kernel is the intersection of the kernels at enclosed spectral values. -/
theorem ker_resolventCircleIntegral (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    (resolventCircleIntegral hp φ c r).ker =
      ⨅ z ∈ enclosedPeriodicSpectrum hp φ c r, (periodicSpectralProjection hp φ z).ker := by
  rw [resolventCircleIntegral_eq_clusterProjection hp φ c r hr hc]
  exact ker_periodicClusterProjection hp φ _

/-- Resolvent circles enclosing the same spectral values give the same operator,
even when their centers differ. -/
theorem resolventCircleIntegral_eq_of_enclosed_eq (hp : p ≠ ⊤) (φ : PairSpace p)
    (c d : ℂ) (r R : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hc : sphere c r ⊆ resolventSet hp φ) (hd : sphere d R ⊆ resolventSet hp φ)
    (he : enclosedPeriodicSpectrum hp φ c r = enclosedPeriodicSpectrum hp φ d R) :
    resolventCircleIntegral hp φ c r = resolventCircleIntegral hp φ d R := by
  rw [resolventCircleIntegral_eq_clusterProjection hp φ c r hr hc,
    resolventCircleIntegral_eq_clusterProjection hp φ d R hR hd, he]

/-- A contour enclosing exactly one spectral value gives its individual root-space projection. -/
theorem resolventCircleIntegral_eq_projection_of_singleton (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (he : enclosedPeriodicSpectrum hp φ c r = {z}) :
    resolventCircleIntegral hp φ c r = periodicSpectralProjection hp φ z := by
  rw [resolventCircleIntegral_eq_clusterProjection hp φ c r hr hc, he]
  simp [periodicClusterProjection]

end NLS.ZakharovShabat
