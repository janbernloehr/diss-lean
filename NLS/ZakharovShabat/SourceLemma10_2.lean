import NLS.ZakharovShabat.SourceLemma10_1
import NLS.ZakharovShabat.SourceLemma10_2Sequences
import NLS.ZakharovShabat.SourceSimpleSpectralDomain

/-!
# Lemma 10.2 on one common almost-real source domain

The actual periodic power sums, midpoint, squared gap, and joint pair
factor are analytic on the same domain as quantitative isolation and
all simple ordinary boundary and critical coordinates. Full midpoint
and squared-gap sequences have locally uniform bounds and tails in
the original source topology, including the half exponent below one.
-/

noncomputable section
open Set Metric Filter
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All clauses and the preceding simple-root assertions on one common domain. -/
structure SourceLemma10_2Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  isolation : ∀ ψ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ ψ ∈ V ∧ V ⊆ W ∧
    ∃ D c, SourceIsolatingNeighborhoods hp hp1 V D c
  power_sums : ∀ n : ℤ, ∀ k : ℕ, AnalyticOnNhd ℂ (fun χ : CoeffPair p =>
    (canonicalPeriodicLeft hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^k+
      (canonicalPeriodicRight hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^k) W
  midpoint : ∀ n : ℤ, AnalyticOnNhd ℂ (fun χ : CoeffPair p =>
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n) W
  squared_gap : ∀ n : ℤ, AnalyticOnNhd ℂ (fun χ : CoeffPair p =>
    (canonicalPeriodicGap hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2) W
  joint_factor : ∀ n : ℤ, AnalyticOnNhd ℂ (fun q : ℂ × CoeffPair p =>
    (canonicalPeriodicLeft hp hp1 (periodOnePotential q.2) (periodOnePotential_mem q.2) n-q.1)*
      (canonicalPeriodicRight hp hp1 (periodOnePotential q.2) (periodOnePotential_mem q.2) n-q.1))
    (univ ×ˢ W)
  uniform_sequences : ∀ φ ∈ W, ∀ η : ℝ, 0 < η →
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧ ∃ N : ℕ, 2 ≤ N ∧ ∃ R : ℝ, 0 ≤ R ∧
      ∀ ψ ∈ U, ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R ∧
        ‖sourcePeriodicSquaredGapSequence hp hp1 ψ‖ ≤ R^2 ∧
        ∀ M : ℕ, N ≤ M →
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ-
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M) (sourcePeriodicMidpointDisplacement hp hp1 ψ)‖ ≤ η ∧
          ‖sourcePeriodicSquaredGapSequence hp hp1 ψ-
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M) (sourcePeriodicSquaredGapSequence hp hp1 ψ)‖ ≤ η^2

  simplicity : SourceSimpleSpectralDomainData hp hp1 W

/-- Restricting the nearby sources preserves a common isolating family and its constant. -/
theorem SourceIsolatingNeighborhoods.mono {hp : p ≠ ⊤} {hp1 : 1 < p}
    {V U : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (h : SourceIsolatingNeighborhoods hp hp1 V D c) (hUV : U ⊆ V) :
    SourceIsolatingNeighborhoods hp hp1 U D c :=
  { h with cluster := fun ψ hψ => h.cluster ψ (hUV hψ)
           gap := fun ψ hψ => h.gap ψ (hUV hψ) }

/-- Lemma 10.2, including common-domain isolation and all simple spectral coordinates. -/
theorem sourceLemma10_2 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_2Data hp hp1 W := by
  obtain ⟨W₀,hW₀open,_,hR₀,hlocal⟩ := sourceLemma10_1 hp hp1
  obtain ⟨W,hWopen,hWconn,hR,hWW₀,hsimple⟩ :=
    exists_sourceSimpleSpectralDomain_within hp hp1 W₀ hW₀open hR₀
  have hA (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        (canonicalPeriodicGap hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2) ψ := by
    obtain ⟨V,hVopen,_,hψV,_,φ,_,N,ε,hε,_,c,hD⟩ := hlocal ψ (hWW₀ hψ)
    exact analyticAt_canonicalPeriodicMidpoint_squaredGap_of_sourceIsolating
      hp hp1 φ ψ N ε hε V hVopen hψV hD.cluster hD.disjoint n
  refine ⟨W,hWopen,hWconn,hR,?_,?_,?_,?_,?_,?_,hsimple⟩
  · intro ψ hψ
    obtain ⟨V,hVo,hVc,hψV,hVW,φ,_,N,ε,_,_,c,hD⟩ := hlocal ψ (hWW₀ hψ)
    obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp ((hVo.inter hWopen).mem_nhds ⟨hψV,hψ⟩)
    exact ⟨ball ψ r,isOpen_ball,isConnected_ball hr,mem_ball_self hr,
      (fun χ hχ => (hrV hχ).2),_,c,hD.mono (fun χ hχ => (hrV hχ).1)⟩
  · intro n k ψ hψ
    obtain ⟨hm,hg⟩ := hA ψ hψ n
    have h := analyticAt_symmetricPairPowerSum hm hg k
    apply h.congr
    filter_upwards with χ
    unfold canonicalPeriodicMidpoint canonicalPeriodicGap
    have hsq :
        (canonicalPeriodicRight hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n-
          canonicalPeriodicLeft hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2 =
        (canonicalPeriodicLeft hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n-
          canonicalPeriodicRight hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2 := by ring
    rw [hsq]
    exact symmetricPairPowerSum_eq _ _ k
  · intro n ψ hψ
    exact (hA ψ hψ n).1
  · intro n ψ hψ
    exact (hA ψ hψ n).2
  · intro n q hq
    obtain ⟨hm,hg⟩ := hA q.2 hq.2 n
    have hmj := hm.comp (analyticAt_snd (p := q))
    have hgj := hg.comp (analyticAt_snd (p := q))
    have hpoly := (hmj.sub analyticAt_fst).pow 2 |>.sub (hgj.div_const (c := (4 : ℂ)))
    exact hpoly.congr (Eventually.of_forall fun t =>
      (sourcePeriodicPair_factorization hp hp1 t.2 n t.1).symm)
  · intro φ hφ η hη
    obtain ⟨U,hU,hφU,N,hN,R,hR,h⟩ := exists_uniform_sourceLemma10_2_sequences hp hp1 φ hη
    exact ⟨U ∩ W,hU.inter hWopen,⟨hφU,hφ⟩,inter_subset_right,N,hN,R,hR,fun ψ hψ => h ψ hψ.1⟩

end NLS.ZakharovShabat
