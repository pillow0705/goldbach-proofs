import Mathlib

theorem Conjectures.Goldbach.BeaumontDenseExactObstruction :
    ∃ A : Set ℝ, Dense A ∧ (0:ℝ) ∈ closure A ∧ (0:ℝ) ∉ A := by
  refine ⟨({0} : Set ℝ)ᶜ, ?_, ?_, by simp⟩
  · exact dense_compl_singleton 0
  · exact (dense_compl_singleton (0 : ℝ)).closure_eq.symm ▸ Set.mem_univ 0
