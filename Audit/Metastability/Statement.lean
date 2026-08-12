/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Metastability

/-! Shared exact proposition for the rounded-metastability comparator. -/

namespace AbsorptionCutoff.StatementAudit.Metastability

open Filter MeasureTheory Topology

/-- The complete Pi-type of paper `thm:rounded-qualitative-metastability`. -/
def RoundedQualitativeMetastabilityStatement : Prop :=
  ∀ {A ρ : ℝ}, 0 < ρ → ρ < 1 →
    roundedExistenceThreshold ρ < A →
    ∃ h : ℝ, h ∈ roundedPositiveDriftSet A ρ ∧
      IsRightmostRoundedPositiveDriftComponent A ρ h ∧
      let Ccomp := roundedPositiveDriftComponent A ρ h
        ∃ η₀ : ℝ, 0 < η₀ ∧
          sInf Ccomp < sSup Ccomp - η₀ ∧
          sSup Ccomp + η₀ < roundedRadiusBound ρ ∧
          (∀ u ∈ Set.Ioc (sSup Ccomp) (sSup Ccomp + η₀),
            roundedMeanMap A ρ u < u) ∧
          ((∀ (B : Set ℝ), IsCompact B →
              B ⊆ Set.Ioc (sInf Ccomp) (sSup Ccomp) →
              ∀ η : ℝ, 0 < η → η < η₀ →
                ∃ Tη : ℕ, ∃ C c₀ c₁ : ℝ,
                  0 < C ∧ 0 < c₀ ∧ 0 < c₁ ∧ c₁ < c₀ ∧
                  (∀ (N : ℕ), 0 < N → ∀ x : Fin N → ℝ,
                    roundedRadiusSq ρ N x ∈ B →
                    (markovPathMeasure
                        (Measure.dirac (roundedRadiusSq ρ N x))
                        (Hkernel A ρ N)).real
                        {ω : ℕ → ℝ |
                          |ω Tη - sSup Ccomp| > η / 2} ≤
                      C * Real.exp (-c₀ * N)) ∧
                  (∀ (N : ℕ), 0 < N → ∀ x : Fin N → ℝ,
                    roundedRadiusSq ρ N x ∈ B → ∀ T : ℕ,
                    (markovPathMeasure
                        (Measure.dirac (roundedRadiusSq ρ N x))
                        (Hkernel A ρ N)).real
                        (metastableExitEvent (sSup Ccomp) η Tη T) ≤
                      C * (1 + T) * Real.exp (-c₀ * N)) ∧
                  (∀ x : ∀ N : ℕ, Fin N → ℝ,
                    (∀ N, roundedRadiusSq ρ N (x N) ∈ B) →
                    Tendsto
                      (fun N : ℕ =>
                        (markovPathMeasure (Measure.dirac (x N))
                            (roundedPkernel A ρ N)).real
                          {ω |
                            ((Tη + ⌊Real.exp (c₁ * N)⌋₊ : ℕ) :
                                WithTop ℕ) <
                              absorptionTime
                                (fun (s : ℕ)
                                  (ω : ℕ → (Fin N → ℝ)) => ω s) ω})
                      atTop (𝓝 1))) ∧
            ∀ (N : ℕ), 0 < N → ∀ x ∈ roundedVectorStateSpace ρ N,
              ∀ᵐ ω ∂markovPathMeasure (Measure.dirac x)
                  (roundedPkernel A ρ N),
                absorptionTime
                  (fun (s : ℕ) (ω : ℕ → (Fin N → ℝ)) => ω s) ω ≠ ⊤)

end AbsorptionCutoff.StatementAudit.Metastability
