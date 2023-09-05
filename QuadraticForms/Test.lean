import Mathlib.LinearAlgebra.QuadraticForm.Basic

variable (K : Type) [Field K]
variable (m : ℕ)
example : Module K ((Fin m) → K) := by
  exact Pi.module (Fin m) (fun _ => K) K

def q : QuadraticForm K (Fin m → K) where
  toFun := _
  toFun_smul := _
  exists_companion' := _

-- def WittMonoid := { nq : ∀ (n : ℕ), (QuadraticForm K (Fin n → K)) }

