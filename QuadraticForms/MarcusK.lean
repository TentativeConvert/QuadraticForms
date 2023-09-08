import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional

variable (K L : Type) [Field K] [Field L]
variable (m : ℕ)

example : Module K ((Fin m) → K) := by
  exact Pi.module (Fin m) (fun _ => K) K

open scoped LinearMap
open FiniteDimensional
open Set


structure FinDimVecSpaces (K : Type) [Field K] where
  carrier : Type
  isAddCommGroup : AddCommGroup carrier
  isModule : Module K carrier
  isFinDim : FiniteDimensional K carrier

attribute [instance] FinDimVecSpaces.isAddCommGroup FinDimVecSpaces.isModule FinDimVecSpaces.isFinDim

example : Nonempty ℕ := by use 3

instance VecSpacesUptoEquiv : Setoid ( FinDimVecSpaces K) where
  r := λ V W ↦ Nonempty (V.carrier ≃ₗ[K] W.carrier)
  iseqv := {
    refl := by 
      intro V
      exact nonempty_linearEquiv_of_rank_eq rfl
      done
    symm := by
      intro V W h
      obtain φ := Classical.choice h
      obtain φ' : (W.carrier ≃ₗ[K] V.carrier) := LinearEquiv.symm φ
      exact ⟨φ'⟩  --OR: exact Nonempty.intro φ'
    trans := by --fun hx hy => hx.trans hy
      intro U V W h₁ h₂
      obtain φ₁ := Classical.choice h₁
      obtain φ₂ := Classical.choice h₂
      obtain φ' : (U.carrier ≃ₗ[K] W.carrier) := LinearEquiv.trans φ₁ φ₂
      exact ⟨φ'⟩
  }

def MyNat := Quotient (VecSpacesUptoEquiv K)

def MyKn (n : ℕ) : FinDimVecSpaces K := ⟨(Fin n → K), by exact Pi.addCommGroup, by exact Pi.module (Fin n) (fun _ => K) K, by exact
  Module.Finite.pi ⟩

#check MyKn

example : FinDimVecSpaces K := MyKn K 3

#check VecSpacesUptoEquiv K

-- example (n : ℕ) : MyNat K := Quotient.mk (VecSpacesUptoEquiv K) (MyKn K n)
--def F : ℕ → MyNat K := fun n ↦ Quotient.mk (VecSpacesUptoEquiv K) (MyKn K n)
def F : ℕ → MyNat K := fun n ↦ ⟦ MyKn K n ⟧

--noncomputable def G : FinDimVecSpaces K → ℕ := fun V ↦ finrank K V.carrier

example : FinDimVecSpaces K := MyKn K 3
noncomputable example : ℕ := FiniteDimensional.finrank K (MyKn K 3).carrier
noncomputable example (C : MyNat K) : ℕ := FiniteDimensional.finrank K (Quotient.out C).carrier

lemma eq_rank_of_iso (V W : Type) 
[AddCommGroup V] [Module K V] [FiniteDimensional K V] 
[AddCommGroup W] [Module K W] [FiniteDimensional K W] 
(h : Nonempty (V ≃ₗ[K] W)) : FiniteDimensional.finrank K V = FiniteDimensional.finrank K W := by
  exact Iff.mp nonempty_linearEquiv_iff_finrank_eq h
  done


theorem F_bijection : Function.Bijective (F K):= by
  let rank' : MyNat K → ℕ := Quotient.lift (fun V ↦ FiniteDimensional.finrank K V.carrier) (fun V W ↦ eq_rank_of_iso K V.carrier W.carrier)
  have h : ∀ (V : MyNat K), rank' ⟦V⟧ = (FiniteDimensional.finrank K V.carrier) := by
    sorry
  apply Function.bijective_iff_has_inverse.2
  use rank'
  constructor
  · intro n
    simp [F,MyKn]
  · intro C
    simp [F,MyKn]
    done
  done



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

