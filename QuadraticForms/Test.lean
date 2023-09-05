import Mathlib.LinearAlgebra.QuadraticForm.Basic

open Real

variable (K : Type) [Field K]
variable (m : ℕ)

example : Module K ((Fin m) → K) := by
  exact Pi.module (Fin m) (fun _ => K) K

def example_qf : QuadraticForm K (Fin m → K) where
  toFun := sorry
  toFun_smul := sorry
  exists_companion' := sorry

structure QuadForms' where
  M : Type
  is_add_comm_monoid : AddCommMonoid M
  is_module : Module K M
  q : QuadraticForm K M


example (T : Type) [AddCommMonoid T] (x y : T) : x + y = 0 := by
  sorry
done

structure QuadForms where
  n : ℕ
  q : QuadraticForm K (Fin n → K)

instance : Setoid (QuadForms K) where
  r := 
  iseqv := sorry

#check QuadForms


instance QuadFormsMonoid : AddCommMonoid (QuadForms K) where
  add := _
  add_assoc := _
  zero := _
  zero_add := _
  add_zero := _
  add_comm := _

