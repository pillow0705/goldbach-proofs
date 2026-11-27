import Mathlib

theorem Conjectures.Goldbach.BeaumontDenseOpenHit :
    ∀ {X : Type} [TopologicalSpace X] (O U : Set X), Dense O → IsOpen U → U.Nonempty → (O ∩ U).Nonempty := by
  intro X inst O U hd hu hU
  simpa only [Set.inter_comm U O] using hd.inter_open_nonempty U hu hU
