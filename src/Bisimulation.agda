{-# OPTIONS --without-K --guardedness --safe #-}
open import Level using (Level; _⊔_; 0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_) renaming (refl to ≡refl)
open import Relation.Unary using (Pred)

module Bisimulation where

module Deterministic where
    record Automaton {p q : Level} (Σ : Set p) (A : Set q) : Set (p ⊔ q) where
        constructor anAutomaton
        field
            trans : A → Σ → A
            acc : A → Bool
    
    record Bisimilarity {p q : Level} {Σ : Set p} {A : Set q} (Å : Automaton Σ A) (xy : A × A) : Set (p ⊔ q) where
        coinductive
        field
            trans : ∀ (a : Σ) → Bisimilarity Å ((Automaton.trans Å (proj₁ xy) a) , (Automaton.trans Å (proj₂ xy) a))
            acc : Automaton.acc Å (proj₁ xy) ≡ Automaton.acc Å (proj₂ xy)

    record _is-a-bisimulation-on_ {p q : Level} {Σ : Set p} {A : Set q} (R : Pred {q} (A × A) (p ⊔ q)) (Å : Automaton Σ A)  : Set (p ⊔ q) where
        constructor bisimulation-proof
        field
            proof-acc : ∀ {x y} → R (x , y) → (Automaton.acc Å x ≡ Automaton.acc Å y)
            proof-trans : ∀ {x y} → R (x , y) → ∀ a → R (Automaton.trans Å x a , Automaton.trans Å y a)
    
    bisimulation⊆bisimilarity : {p q : Level} {Σ : Set p} {A : Set q} (Å : Automaton Σ A) (R : Pred {q} (A × A) (p ⊔ q))
        → (R-is-bisimulation : R is-a-bisimulation-on Å)
        → ∀ {x y} → R (x , y) → Bisimilarity Å (x , y)
    Bisimilarity.acc   (bisimulation⊆bisimilarity Å R (bisimulation-proof prf-acc prf-trans) xRy) = prf-acc xRy
    Bisimilarity.trans (bisimulation⊆bisimilarity Å R (bisimulation-proof prf-acc prf-trans) xRy) a =
        bisimulation⊆bisimilarity Å R (bisimulation-proof prf-acc prf-trans) (prf-trans xRy a)

    bisimilarity-is-a-bisimulation : {p q : Level} {Σ : Set p} {A : Set q} (Å : Automaton Σ A)
        → (Bisimilarity Å) is-a-bisimulation-on Å
    bisimilarity-is-a-bisimulation Å = bisimulation-proof
        (λ xy-bisimilar → Bisimilarity.acc xy-bisimilar)
        (λ xy-bisimilar → Bisimilarity.trans xy-bisimilar)
    
    module Example where
        data Σ : Set where
            a : Σ
            b : Σ
        
        data A : Set where
            x : A
            y : A
            z : A
        
        Åacc : A → Bool
        Åacc x = false
        Åacc y = false
        Åacc z = true

        Åtrans : A → Σ → A
        Åtrans x a = z
        Åtrans x b = x
        Åtrans y a = z
        Åtrans y b = y
        Åtrans z a = y
        Åtrans z b = x
        
        Å : Automaton Σ A
        Å = anAutomaton Åtrans Åacc

        xBy : Bisimilarity Å (x , y)
        zBz : Bisimilarity Å (z , z)
        xBx : Bisimilarity Å (x , x)
        yBy : Bisimilarity Å (y , y)
        
        Bisimilarity.acc   xBy = ≡refl
        Bisimilarity.trans xBy a = zBz
        Bisimilarity.trans xBy b = xBy
        
        Bisimilarity.acc   zBz = ≡refl
        Bisimilarity.trans zBz a = yBy
        Bisimilarity.trans zBz b = xBx
        
        Bisimilarity.acc   xBx = ≡refl
        Bisimilarity.trans xBx a = zBz
        Bisimilarity.trans xBx b = xBx
        
        Bisimilarity.acc   yBy = ≡refl
        Bisimilarity.trans yBy a = zBz
        Bisimilarity.trans yBy b = yBy
