import NLS.SequenceSpaces.OrderedPairStripPropagation
import NLS.ZakharovShabat.PeriodicEndpointSlots

/-! # Inward propagation of counted endpoint pairs

Strictly localized anchors and two occurrences per adjacent strip identify
the next pair inward. The argument uses real-part order only.
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- There is one slot strictly between a left slot and the following left slot. -/
theorem endpoint_slot_between_left (n : ℤ) (k : ℤ ×ₗ Fin 2)
    (hl : toLex (n,0) < k) (hr : k < toLex (n+1,0)) : k = toLex (n,1) := by
  obtain ⟨⟨i,a⟩,rfl⟩ := toLex.surjective k
  simp only [Prod.Lex.toLex_lt_toLex] at hl hr
  have hi : i = n := by omega
  have ha : a = 1 := by apply Fin.ext; omega
  simp only [hi,ha]

/-- There is one slot strictly between a right slot and the following right slot. -/
theorem endpoint_slot_between_right (n : ℤ) (k : ℤ ×ₗ Fin 2)
    (hl : toLex (n,1) < k) (hr : k < toLex (n+1,1)) : k = toLex (n+1,0) := by
  obtain ⟨⟨i,a⟩,rfl⟩ := toLex.surjective k
  simp only [Prod.Lex.toLex_lt_toLex] at hl hr
  have hi : i = n+1 := by omega
  have ha : a = 0 := by apply Fin.ext; omega
  simp only [hi,ha]

/-- The strip is the closed interval between its two real boundaries. -/
theorem mem_resonantStrip_iff_re_interval (n : ℤ) (z : ℂ) :
    z ∈ resonantStrip n ↔ z.re ∈ Set.Icc (Real.pi*n-Real.pi/2) (Real.pi*n+Real.pi/2) := by
  change |z.re-Real.pi*n| ≤ Real.pi/2 ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- A refined-disc point is strictly separated from both strip boundaries. -/
theorem refinedResonantDisk_re_interval (n : ℤ) (z : ℂ) (hz : z ∈ refinedResonantDisk n) :
    Real.pi*n-Real.pi/4 < z.re ∧ z.re < Real.pi*n+Real.pi/4 := by
  have hnorm : ‖z-(Real.pi:ℂ)*n‖ < Real.pi/4 := by simpa only [refinedResonantDisk, Metric.mem_ball, dist_eq_norm] using hz
  have h := (Complex.abs_re_le_norm (z-(Real.pi:ℂ)*n)).trans_lt hnorm
  have h' : |z.re-Real.pi*n| < Real.pi/4 := by simpa using h
  obtain ⟨hl,hr⟩ := abs_lt.mp h'
  constructor <;> linarith

/-- A known pair in strip n+1 identifies the preceding ordered pair in strip n. -/
theorem endpoint_pair_strip_step_left (N : ℕ) (n : ℤ) (ξ η : ℤ → ℂ)
    (hn : n.natAbs ≤ N) (hn1 : (n+1).natAbs ≤ N)
    (horder : Monotone (fun k : ℤ ×ₗ Fin 2 => (periodicEndpointSlot ξ η k).re))
    (hcount : ((centralPeriodicSlots N).filter (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip n)).card = 2)
    (hcount1 : ((centralPeriodicSlots N).filter (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip (n+1))).card = 2)
    (hx : ξ (n+1) ∈ refinedResonantDisk (n+1)) (hy : η (n+1) ∈ refinedResonantDisk (n+1)) :
    ξ n ∈ resonantStrip n ∧ η n ∈ resonantStrip n := by
  have hxre := refinedResonantDisk_re_interval (n+1) _ hx
  have hyre := refinedResonantDisk_re_interval (n+1) _ hy
  have hcount' := hcount
  have hcount1' := hcount1
  simp only [mem_resonantStrip_iff_re_interval] at hcount' hcount1'
  have hmid : Real.pi*((n+1:ℤ):ℝ)-Real.pi/2 = Real.pi*n+Real.pi/2 := by push_cast; ring
  rw [hmid] at hcount1'
  have h := NLS.ordered_pair_step_left (centralPeriodicSlots N) (fun k => (periodicEndpointSlot ξ η k).re)
    (horder.monotoneOn _) (toLex (n,0)) (toLex (n,1)) (toLex (n+1,0)) (toLex (n+1,1))
    (by simpa using hn) (by simpa using hn) (by simpa using hn1) (by simpa using hn1)
    (by simp [Prod.Lex.toLex_lt_toLex]) (by simp [Prod.Lex.toLex_lt_toLex])
    (by simp [Prod.Lex.toLex_lt_toLex]) (endpoint_slot_between_left n)
    _ _ _ hcount' hcount1' (by simp only [periodicEndpointSlot_left]; push_cast at hxre; linarith [Real.pi_pos])
    (by simpa only [periodicEndpointSlot_left] using hxre.2.le.trans (by linarith [Real.pi_pos]))
    (by simp only [periodicEndpointSlot_right]; push_cast at hyre; linarith [Real.pi_pos])
    (by simpa only [periodicEndpointSlot_right] using hyre.2.le.trans (by linarith [Real.pi_pos]))
  simpa only [periodicEndpointSlot_left, periodicEndpointSlot_right, ← mem_resonantStrip_iff_re_interval] using h

/-- A known pair in strip n identifies the following ordered pair in strip n+1. -/
theorem endpoint_pair_strip_step_right (N : ℕ) (n : ℤ) (ξ η : ℤ → ℂ)
    (hn : n.natAbs ≤ N) (hn1 : (n+1).natAbs ≤ N)
    (horder : Monotone (fun k : ℤ ×ₗ Fin 2 => (periodicEndpointSlot ξ η k).re))
    (hcount : ((centralPeriodicSlots N).filter (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip n)).card = 2)
    (hcount1 : ((centralPeriodicSlots N).filter (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip (n+1))).card = 2)
    (hx : ξ n ∈ refinedResonantDisk n) (hy : η n ∈ refinedResonantDisk n) :
    ξ (n+1) ∈ resonantStrip (n+1) ∧ η (n+1) ∈ resonantStrip (n+1) := by
  have hxre := refinedResonantDisk_re_interval n _ hx
  have hyre := refinedResonantDisk_re_interval n _ hy
  have hcount' := hcount
  have hcount1' := hcount1
  simp only [mem_resonantStrip_iff_re_interval] at hcount' hcount1'
  have hmid : Real.pi*((n+1:ℤ):ℝ)-Real.pi/2 = Real.pi*n+Real.pi/2 := by push_cast; ring
  rw [hmid] at hcount1'
  have h := NLS.ordered_pair_step_right (centralPeriodicSlots N) (fun k => (periodicEndpointSlot ξ η k).re)
    (horder.monotoneOn _) (toLex (n,0)) (toLex (n,1)) (toLex (n+1,0)) (toLex (n+1,1))
    (by simpa using hn) (by simpa using hn) (by simpa using hn1) (by simpa using hn1)
    (by simp [Prod.Lex.toLex_lt_toLex]) (by simp [Prod.Lex.toLex_lt_toLex])
    (by simp [Prod.Lex.toLex_lt_toLex]) (endpoint_slot_between_right n)
    _ _ _ hcount' hcount1'
    (by simpa only [periodicEndpointSlot_left] using (by linarith [Real.pi_pos] : Real.pi*n-Real.pi/2 ≤ (ξ n).re))
    (by simpa only [periodicEndpointSlot_left] using (by linarith [Real.pi_pos] : (ξ n).re ≤ Real.pi*n+Real.pi/2))
    (by simpa only [periodicEndpointSlot_right] using (by linarith [Real.pi_pos] : Real.pi*n-Real.pi/2 ≤ (η n).re))
    (by simpa only [periodicEndpointSlot_right] using (by linarith [Real.pi_pos] : (η n).re < Real.pi*n+Real.pi/2))
  rw [← hmid] at h
  simpa only [periodicEndpointSlot_left, periodicEndpointSlot_right, ← mem_resonantStrip_iff_re_interval] using h

end NLS.ZakharovShabat
