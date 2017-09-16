open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection

open import Control.Monad.State

module Elaboration.Monad where

record ElabState : Set where
  constructor ElabS
  field
    goal : Type
    ctx  : List (Arg Type)
    term : Term

open ElabState

Elab = StateT ElabState TC

macro
  %runElab : Elab ⊤ → Term → TC ⊤
  %runElab e h = do t  ← inferType h
                 -| c  ← getContext
                 -| st ← runStateT e (ElabS t (reverse c) h)
                 -| return tt

-- introduce a variable of a pi type
intro : Elab ⊤
runStateT intro (ElabS g ctx t) with g
... | pi a (Abs.abs s t₁) =
  inContext (ctx ++ [ a ]) (do m  ← newMeta t₁
                            -| (unify t (lam (getVisibility a) (Abs.abs "" m)))
                            ~| return (tt , ElabS t₁ (ctx ++ [ a ]) m))
... | _ = typeError (strErr "Can't ′intro′ a non function type ′" ∷
                     termErr g ∷ strErr "′." ∷ [])

-- fill the current goal with the given Term
fill : Term → Elab ⊤
runStateT (fill t) (ElabS goal ctx term) =
  inContext ctx (do unify term t
                 ~| return (tt , (ElabS goal ctx t)))

debug : ∀ {a : Set} → Elab a
runStateT debug (ElabS g ctx t) =
  inContext ctx (do c ← quoteTC ctx >>= normalise
                 -| typeError (strErr "Goal: "    ∷ termErr g ∷ newLine ∷
                               strErr "Context: " ∷ termErr c ∷ newLine ∷
                               strErr "Term: "    ∷ termErr t ∷ []))
    where
      newLine = strErr "\n"

-- the tactic that always succeds
success : Elab ⊤
success = return tt

-- the tactic that fails with a given message
fail : String → Elab ⊤
runStateT (fail str) s = typeError [ strErr str  ]

-- try the first tactic, if fails try the second one
try : ∀ {a} → Elab a → Elab a → Elab a
runStateT (try e1 e2) s = catchTC (runStateT e1 s) (runStateT e2 s) 

-- introduce as many variables as possible
introsN : Nat → Elab ⊤
introsN 0       = fail "`intros` exhausted"
introsN (suc n) = try (intro >> introsN n) success

intros : Elab ⊤
intros = introsN 100

mk : Elab ⊤
mk = intros
  ~| fill (lit (nat (0)))

mkId : Elab ⊤
mkId = do intro
       ~| fill (var 0 [])

idNat : Nat → Nat
idNat = %runElab mkId

idString : String → String → String
idString = %runElab (intro >> mkId)

mkConstE : Elab ⊤
mkConstE = do intro
           ~| intro
           ~| fill (var 2 [])

constNat : Nat → Nat → Nat
constNat = %runElab mkConstE

nat0 : Nat
nat0 = %runElab mk

nat1 : Nat → Nat → Nat → Nat
nat1 = %runElab mk

nat2 : Nat
nat2 = (%runElab mkId) 4
