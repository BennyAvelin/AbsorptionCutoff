/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib

/-!
# Nearest-grid rounding

Formalizes the coordinatewise nearest-grid rounding map `Q_ρ` from the paper
(§2, "Gaussian squared-radius chains and common scalar estimates"), with ties
broken toward the grid point of smaller absolute value.

## Main definitions
* `AbsorptionCutoff.Q₁`      — scalar unit-grid rounding `ℝ → ℤ` (round half toward zero).
* `AbsorptionCutoff.gridRound` — scalar rounding to `ρℤ`.
* `AbsorptionCutoff.Qρ`      — coordinatewise vector rounding to `(ρℤ)^N`.

## Main results (paper eq. after `eq:rounded-chain`)
* `Q₁_zero_iff`      — `Q₁ u = 0 ↔ |u| ≤ 1/2`.
* `Q₁_sub_le`        — `|Q₁ u - u| ≤ 1/2`.
* `gridRound_zero_iff`, `gridRound_sub_le` — the `ρ`-scaled versions.
-/

namespace AbsorptionCutoff

/-- Scalar nearest-integer rounding on the unit grid, with ties broken toward the
grid point of smaller absolute value (round half toward zero). -/
noncomputable def Q₁ (u : ℝ) : ℤ :=
  if 0 ≤ u then ⌈u - 2⁻¹⌉ else -⌈-u - 2⁻¹⌉

/-- A point lands in the zero bin iff it is within `1/2` of the origin. -/
lemma Q₁_zero_iff (u : ℝ) : Q₁ u = 0 ↔ |u| ≤ 2⁻¹ := by
  unfold Q₁
  by_cases hu : 0 ≤ u
  · rw [if_pos hu, abs_of_nonneg hu, Int.ceil_eq_zero_iff]
    exact ⟨fun ⟨_, h2⟩ => by linarith, fun h => ⟨by linarith, by linarith⟩⟩
  · have hu' : u < 0 := not_le.mp hu
    rw [if_neg hu, neg_eq_zero, abs_of_neg hu', Int.ceil_eq_zero_iff]
    exact ⟨fun ⟨_, h2⟩ => by linarith, fun h => ⟨by linarith, by linarith⟩⟩

/-- The rounding error is at most `1/2`. -/
lemma Q₁_sub_le (u : ℝ) : |(Q₁ u : ℝ) - u| ≤ 2⁻¹ := by
  unfold Q₁
  by_cases hu : 0 ≤ u
  · rw [if_pos hu]
    have h1 : (u - 2⁻¹ : ℝ) ≤ ⌈u - 2⁻¹⌉ := Int.le_ceil _
    have h2 : (⌈u - 2⁻¹⌉ : ℝ) < (u - 2⁻¹) + 1 := Int.ceil_lt_add_one _
    rw [abs_le]; exact ⟨by linarith, by linarith⟩
  · rw [if_neg hu]
    have h1 : (-u - 2⁻¹ : ℝ) ≤ ⌈-u - 2⁻¹⌉ := Int.le_ceil _
    have h2 : (⌈-u - 2⁻¹⌉ : ℝ) < (-u - 2⁻¹) + 1 := Int.ceil_lt_add_one _
    push_cast
    rw [abs_le]; exact ⟨by linarith, by linarith⟩

/-- `Q₁` is measurable (a step function: `Int.ceil` on either sign branch). Used to
build the rounded squared-radius chain kernel. -/
lemma measurable_Q₁ : Measurable Q₁ := by
  unfold Q₁
  apply Measurable.ite (measurableSet_le measurable_const measurable_id)
  · exact Int.measurable_ceil.comp (measurable_id.sub measurable_const)
  · exact (Int.measurable_ceil.comp (measurable_id.neg.sub measurable_const)).neg

/-- Scalar rounding to the grid `ρℤ`. -/
noncomputable def gridRound (ρ u : ℝ) : ℝ := ρ * (Q₁ (u / ρ) : ℝ)

/-- A point lands in the zero bin of the `ρ`-grid iff it is within `ρ/2` of the origin. -/
lemma gridRound_zero_iff {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    gridRound ρ u = 0 ↔ |u| ≤ ρ / 2 := by
  unfold gridRound
  rw [mul_eq_zero, or_iff_right (ne_of_gt hρ)]
  rw [show (0 : ℝ) = ((0 : ℤ) : ℝ) by norm_num, Int.cast_inj, Q₁_zero_iff,
    abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  constructor <;> intro h <;> nlinarith [h]

/-- The `ρ`-grid rounding error is at most `ρ/2`. -/
lemma gridRound_sub_le {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    |gridRound ρ u - u| ≤ ρ / 2 := by
  have hne : ρ ≠ 0 := ne_of_gt hρ
  have key : |(Q₁ (u / ρ) : ℝ) - u / ρ| ≤ 2⁻¹ := Q₁_sub_le _
  have hrw : gridRound ρ u - u = ρ * ((Q₁ (u / ρ) : ℝ) - u / ρ) := by
    unfold gridRound; field_simp
  rw [hrw, abs_mul, abs_of_pos hρ]
  nlinarith [key, hρ]

/-- Coordinatewise vector rounding to the grid `(ρℤ)^N`. -/
noncomputable def Qρ (ρ : ℝ) {N : ℕ} (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => gridRound ρ (x i)

/-- Coordinatewise characterization of the vector zero bin. -/
lemma Qρ_eq_zero_iff {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (x : Fin N → ℝ) :
    Qρ ρ x = 0 ↔ ∀ i, |x i| ≤ ρ / 2 := by
  unfold Qρ
  rw [funext_iff]
  simp only [Pi.zero_apply]
  exact forall_congr' fun i => gridRound_zero_iff hρ (x i)

end AbsorptionCutoff
