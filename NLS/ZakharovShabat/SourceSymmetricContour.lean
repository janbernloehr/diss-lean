import NLS.ZakharovShabat.SourceIsolatingMultiplicity
import NLS.ZakharovShabat.SymmetricEigenvalues
import NLS.ZakharovShabat.DiscriminantPairFactorization

/-!
# Analytic symmetric periodic coordinates on source isolating discs

Each assigned contour has rank two and encloses exactly the indexed pair.
The first two contour traces therefore recover its midpoint and squared
gap, while the frozen contour makes both expressions analytic in the source
coefficient parameter.
-/

noncomputable section
open Set Metric Complex Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The trace invariants of any assigned source contour are the midpoint
and squared gap of its canonical periodic endpoint pair. -/
theorem sourceIsolatingContour_midpoint_squaredGap_eq_pair
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) :
    let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    let b := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    contourMidpoint hp (periodOnePotential ψ)
      (sourceIsolatingCenter hp hp1 φ N n)
      (sourceIsolatingRadius hp hp1 φ N ε n) = (a+b)/2 ∧
    contourSquaredGap hp (periodOnePotential ψ)
      (sourceIsolatingCenter hp hp1 φ N n)
      (sourceIsolatingRadius hp hp1 φ N ε n) = (a-b)^2 := by
  dsimp
  have hr := (sourceIsolatingRadius_pos hp hp1 φ N ε hε n).le
  have hc := sourceIsolatingSphere_subset_resolventSet hp hp1 φ ψ N ε hε hcluster hdisjoint n
  have hdim := sourceIsolatingContour_rank_two hp hp1 φ ψ N ε hε hcluster hdisjoint n
  have hs := enclosedPeriodicSpectrum_sourceIsolating_eq_pair hp hp1 φ ψ N ε hcluster hdisjoint n
  have h := contourMidpoint_squaredGap_eq_pair hp (periodOnePotential ψ) _ _
    hr hc hdim _ _ hs
  exact ⟨h.1, h.2.1⟩

/-- The frozen midpoint and squared-gap contours are analytic at every
source parameter whose periodic spectrum avoids their boundary. -/
theorem analyticAt_sourceIsolatingContour_midpoint_squaredGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (n : ℤ)
    (hc : sphere (sourceIsolatingCenter hp hp1 φ N n)
      (sourceIsolatingRadius hp hp1 φ N ε n) ⊆
        resolventSet hp (periodOnePotential ψ)) :
    AnalyticAt ℂ (fun χ : CoeffPair p =>
      contourMidpoint hp (periodOnePotential χ)
        (sourceIsolatingCenter hp hp1 φ N n)
        (sourceIsolatingRadius hp hp1 φ N ε n)) ψ ∧
    AnalyticAt ℂ (fun χ : CoeffPair p =>
      contourSquaredGap hp (periodOnePotential χ)
        (sourceIsolatingCenter hp hp1 φ N n)
        (sourceIsolatingRadius hp hp1 φ N ε n)) ψ := by
  have hr := (sourceIsolatingRadius_pos hp hp1 φ N ε hε n).le
  have h := analyticAt_contourMidpoint_and_squaredGap hp (periodOnePotential ψ)
    _ _ hr hc
  exact ⟨h.1.comp (periodOnePotential.analyticAt ψ),
    h.2.comp (periodOnePotential.analyticAt ψ)⟩

/-- On a common source isolating neighborhood, the canonical midpoint and
squared gap are analytic at every parameter, including collapsed gaps. -/
theorem analyticAt_canonicalPeriodicMidpoint_squaredGap_of_sourceIsolating
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (V : Set (CoeffPair p)) (hVopen : IsOpen V) (hψ : ψ ∈ V)
    (hcluster : ∀ χ ∈ V, ∀ m : ℤ, sourceSpectralCluster hp hp1 χ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) :
    AnalyticAt ℂ (fun χ : CoeffPair p =>
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ ∧
    AnalyticAt ℂ (fun χ : CoeffPair p =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2) ψ := by
  let c := sourceIsolatingCenter hp hp1 φ N n
  let r := sourceIsolatingRadius hp hp1 φ N ε n
  have hc := sourceIsolatingSphere_subset_resolventSet hp hp1 φ ψ N ε hε
    (hcluster ψ hψ) hdisjoint n
  have hAn := analyticAt_sourceIsolatingContour_midpoint_squaredGap hp hp1
    φ ψ N ε hε n hc
  have heq1 :
      (fun χ : CoeffPair p => contourMidpoint hp (periodOnePotential χ) c r) =ᶠ[𝓝 ψ]
        (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
          (periodOnePotential χ) (periodOnePotential_mem χ) n) := by
    filter_upwards [hVopen.mem_nhds hψ] with χ hχ
    have h := (sourceIsolatingContour_midpoint_squaredGap_eq_pair hp hp1
      φ χ N ε hε (hcluster χ hχ) hdisjoint n).1
    simpa only [c, r, canonicalPeriodicMidpoint] using h
  have heq2 :
      (fun χ : CoeffPair p => contourSquaredGap hp (periodOnePotential χ) c r) =ᶠ[𝓝 ψ]
        (fun χ : CoeffPair p =>
          (canonicalPeriodicGap hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2) := by
    filter_upwards [hVopen.mem_nhds hψ] with χ hχ
    have h := (sourceIsolatingContour_midpoint_squaredGap_eq_pair hp hp1
      φ χ N ε hε (hcluster χ hχ) hdisjoint n).2
    calc
      contourSquaredGap hp (periodOnePotential χ) c r =
          (canonicalPeriodicLeft hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n -
            canonicalPeriodicRight hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2 := by
        simpa only [c, r] using h
      _ = (canonicalPeriodicGap hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2 := by
        unfold canonicalPeriodicGap
        ring
  exact ⟨hAn.1.congr heq1, hAn.2.congr heq2⟩

/-- On the open connected almost-real source domain, every indexed canonical
periodic midpoint and squared gap is analytic. This is the analyticity
assertion of Lemma 10.2(ii); the sequence asymptotics are separate. -/
theorem exists_global_source_analytic_midpoint_squaredGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        AnalyticAt ℂ (fun χ : CoeffPair p =>
          canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ ∧
        AnalyticAt ℂ (fun χ : CoeffPair p =>
          (canonicalPeriodicGap hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2) ψ := by
  obtain ⟨W, hWopen, hWconnected, hR, hlocal⟩ :=
    exists_global_source_isolating_neighborhood hp hp1
  refine ⟨W, hWopen, hWconnected, hR, ?_⟩
  intro ψ hψ n
  obtain ⟨V, hVopen, _, hψV, _, φ, N, ε, hε, _, hcluster, _, hdisjoint⟩ :=
    hlocal ψ hψ
  exact analyticAt_canonicalPeriodicMidpoint_squaredGap_of_sourceIsolating
    hp hp1 φ ψ N ε hε V hVopen hψV hcluster hdisjoint n

end NLS.ZakharovShabat
