import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional

-- Eric Wieser told me this trick to hide all the annoying proofs from the infoview. Just add this line to the top f your file:
set_option pp.proofs.withType false

variable (K L : Type) [Field K] [Field L]
variable (m : ℕ)

example : Module K ((Fin m) → K) := by
  exact Pi.module (Fin m) (fun _ => K) K

open scoped LinearMap
open FiniteDimensional
open Set


structure fdVecSpaces (K : Type) [Field K] where
  carrier : Type
  isAddCommGroup : AddCommGroup carrier
  isModule : Module K carrier
  isfd : FiniteDimensional K carrier

attribute [instance] fdVecSpaces.isAddCommGroup fdVecSpaces.isModule fdVecSpaces.isfd

def MyKn (n : ℕ) : fdVecSpaces K := ⟨(Fin n → K), by exact Pi.addCommGroup, by exact Pi.module (Fin n) (fun _ => K) K, by exact
  Module.Finite.pi ⟩

--#check MyKn
--example : fdVecSpaces K := MyKn K 3
--example : fdVecSpaces K := MyKn K 3

instance VecSpacesUptoEquiv : Setoid (fdVecSpaces K) where
  r := λ V W ↦  Nonempty (V.carrier ≃ₗ[K] W.carrier)
  iseqv := {
    refl := by 
      intro V
      exact ⟨LinearEquiv.refl K V.carrier⟩ 
      done
    symm := by
      intro V W h
      obtain φ := Classical.choice h
      obtain φ' : (W.carrier ≃ₗ[K] V.carrier) := φ.symm -- equivalently: LinearEquiv.symm φ
      exact ⟨φ'⟩  --OR: exact Nonempty.intro φ'
    trans :=  -- fun hx hy ↦ hx.trans hy  -- does not work here
    by -- fun hx hy => hx.trans hy
      intro U V W h₁ h₂
      obtain φ₁ := Classical.choice h₁
      obtain φ₂ := Classical.choice h₂
      obtain φ' : (U.carrier ≃ₗ[K] W.carrier) := φ₁.trans φ₂ -- equivalently:  LinearEquiv.trans φ₁ φ₂
      exact ⟨φ'⟩
  }

--#check VecSpacesUptoEquiv K

lemma vec_spaces_equiv_iff (V W : fdVecSpaces K) : V ≈ W ↔ Nonempty (V.carrier ≃ₗ[K] W.carrier) := by rfl 

-- the following lemma should be removed since its proved by a single other lemma
lemma eq_rank_of_iso (V W : Type) 
[AddCommGroup V] [Module K V] [FiniteDimensional K V] 
[AddCommGroup W] [Module K W] [FiniteDimensional K W] 
(h : Nonempty (V ≃ₗ[K] W)) : FiniteDimensional.finrank K V = FiniteDimensional.finrank K W := by
  exact Iff.mp nonempty_linearEquiv_iff_finrank_eq h
  done

-- Read about quotients in
--  Mathlib.Data.Quot
--rather than Init.Core
def isoVec := Quotient (VecSpacesUptoEquiv K)


noncomputable def rank' : isoVec K → ℕ := Quotient.lift (fun V ↦ FiniteDimensional.finrank K V.carrier) (fun V W ↦ eq_rank_of_iso K V.carrier W.carrier)
  
-- the following lemma is not used explicitly anywhere
lemma rank'_lifts_finrank : ∀ (V : fdVecSpaces K), rank' K ⟦V⟧ = (FiniteDimensional.finrank K V.carrier) := by
    intro V
    rfl

theorem rank'_is_bijection : Function.Bijective (rank' K) := by
  apply Function.bijective_iff_has_inverse.2
  let F : ℕ → isoVec K := fun n ↦ ⟦ MyKn K n ⟧
  use F
  constructor
  · apply Quotient.ind
    intro V
    apply Quotient.sound
    rw [rank', MyKn,vec_spaces_equiv_iff]
    apply nonempty_linearEquiv_of_rank_eq
    simp
    done
  · intro n
    simp [MyKn,rank'] 
  done

-----------------------------------------------------------------------------
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

#check QuadForms
