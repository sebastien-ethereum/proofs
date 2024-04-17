/-
Syntax
-/

inductive Typ : Type
  | not   : Typ → Typ
  | and   : Typ → Typ → Typ
  | true  : Typ
  | or    : Typ → Typ → Typ
  | false : Typ

inductive Pha : Type
  | C : Pha
  | I : List Typ → Pha
  | O : Typ → Pha

open Pha

inductive Var : α → List α → Type
  | zero : Var a (a :: xs)
  | succ : Var a xs → Var a (x :: xs)

inductive Exp : {J : Type} → J → Pha → List Typ → Type
  | C.halt :
      (j : J) →
      Exp j C γ
  | C.step :
      Exp j (O a) γ →
      Var a γ →
      Exp j C γ
  | I.stable :
      Exp j C γ →
      Exp j (I []) γ
  | I.not :
      Exp j (I as) (a :: γ) →
      Exp j (I (Typ.not a :: as)) γ
  | I.and :
      Exp j (I (a₁ :: a₂ :: as)) γ →
      Exp j (I (Typ.and a₁ a₂ :: as)) γ
  | I.true :
      Exp j (I as) γ →
      Exp j (I (Typ.true :: as)) γ
  | I.or :
      Exp j (I (a₁ :: as)) γ →
      Exp j (I (a₂ :: as)) γ →
      Exp j (I (Typ.or a₁ a₂ :: as)) γ
  | I.false :
      Exp j (I (Typ.false :: as)) γ
  | O.not :
      Exp j (I [a]) γ →
      Exp j (O (Typ.not a)) γ
  | O.and :
      Exp j (O a₁) γ →
      Exp j (O a₂) γ →
      Exp j (O (Typ.and a₁ a₂)) γ
  | O.true :
      Exp j (O Typ.true) γ
  | O.or₁ :
      Exp j (O a₁) γ →
      Exp j (O (Typ.or a₁ a₂)) γ
  | O.or₂ :
      Exp j (O a₂) γ →
      Exp j (O (Typ.or a₁ a₂)) γ



/-
Operational semantics
-/

mutual

  inductive Env : List Typ → Type 2
    | nil  : Env []
    | cons : Clo (I [a]) → Env γ → Env (a :: γ)

  inductive Clo : Pha → Type 2
    | mk : Exp j δ γ → Env γ → Clo δ

end

inductive CloOs : List Typ → Type 2
  | nil  : CloOs []
  | cons : Clo (O a) → CloOs as → CloOs (a :: as)

def lookup : Var a γ → Env γ → Clo (I [a])
  | Var.zero,   Env.cons ci _ => ci
  | Var.succ v, Env.cons _  ρ => lookup v ρ

def apply : Clo (I as) → CloOs as → Clo C
  | ⟨Exp.I.stable ec,  ρi⟩, CloOs.nil                              => ⟨ec, ρi⟩
  | ⟨Exp.I.not ei,     ρi⟩, CloOs.cons ⟨Exp.O.not ei',     ρo⟩ cos => apply ⟨ei, Env.cons ⟨ei', ρo⟩ ρi⟩ cos
  | ⟨Exp.I.and ei,     ρi⟩, CloOs.cons ⟨Exp.O.and eo₁ eo₂, ρo⟩ cos => apply ⟨ei, ρi⟩                    (CloOs.cons ⟨eo₁, ρo⟩ (CloOs.cons ⟨eo₂, ρo⟩ cos))
  | ⟨Exp.I.true ei,    ρi⟩, CloOs.cons ⟨Exp.O.true,        _ ⟩ cos => apply ⟨ei, ρi⟩                    cos
  | ⟨Exp.I.or ei₁ _,   ρi⟩, CloOs.cons ⟨Exp.O.or₁ eo,      ρo⟩ cos => apply ⟨ei₁, ρi⟩                   (CloOs.cons ⟨eo, ρo⟩ cos)
  | ⟨Exp.I.or _   ei₂, ρi⟩, CloOs.cons ⟨Exp.O.or₂ eo,      ρo⟩ cos => apply ⟨ei₂, ρi⟩                   (CloOs.cons ⟨eo, ρo⟩ cos)
termination_by ci _ => let ⟨ei, _⟩ := ci; sizeOf ei

def step : Clo C → Clo C
  | ⟨Exp.C.halt j,    ρ⟩ => ⟨Exp.C.halt j, ρ⟩
  | ⟨Exp.C.step eo v, ρ⟩ => apply (lookup v ρ) (CloOs.cons ⟨eo, ρ⟩ CloOs.nil)



/-
Realizers / Semantic types / Logical predicates
n.b. negative occurrence of ReaO prevents inductive definition
-/

inductive ReaC (p : J → Sort u) : Clo C → Type (max u 2)
  | halt : (j : J) → p j → ReaC p ⟨Exp.C.halt j, ρ⟩
  | step : ReaC p (step ⟨Exp.C.step eo v, ρ⟩) → ReaC p ⟨Exp.C.step eo v, ρ⟩

def ReaO (p : J → Sort u) : (a : Typ) → Clo (O a) → Type (max u 2)
  | Typ.not a,     ⟨Exp.O.not i,       ρ⟩ => {co : Clo (O a)} → ReaO p a co → ReaC p (apply ⟨i, ρ⟩ (CloOs.cons co CloOs.nil))
  | Typ.and a₁ a₂, ⟨Exp.O.and eo₁ eo₂, ρ⟩ => ReaO p a₁ ⟨eo₁, ρ⟩ × ReaO p a₂ ⟨eo₂, ρ⟩
  | Typ.true,      ⟨Exp.O.true,        _⟩ => PUnit
  | Typ.or a₁ _,   ⟨Exp.O.or₁ eo,      ρ⟩ => ReaO p a₁ ⟨eo, ρ⟩
  | Typ.or _  a₂,  ⟨Exp.O.or₂ eo,      ρ⟩ => ReaO p a₂ ⟨eo, ρ⟩

inductive ReaOs (p : J → Sort u) : (as : List Typ) → CloOs as → Type (max u 2)
  | nil  : ReaOs p [] CloOs.nil
  | cons : ReaO p a co → ReaOs p as cos → ReaOs p (a :: as) (CloOs.cons co cos)

def ReaI (p : J → Sort u) (as : List Typ) (ci : Clo (I as)) : Type (max u 2) :=
  {cos : CloOs as} → ReaOs p as cos → ReaC p (apply ci cos)

inductive ReaEnv (p : J → Sort u) : (γ : List Typ) → Env γ → Type (max u 2)
  | nil  : ReaEnv p [] Env.nil
  | cons : ReaI p [a] ci → ReaEnv p γ ρ → ReaEnv p (a :: γ) (Env.cons ci ρ)

def Rea (p : J → Sort u) : {δ : Pha} → Clo δ → Type (max u 2)
  | C    => ReaC p
  | I as => ReaI p as
  | O a  => ReaO p a

def Rea' (p : J → Sort u) {δ : Pha} {γ : List Typ} (e : Exp j' δ γ) : Type (max u 2) :=
  {ρ : Env γ} → ReaEnv p γ ρ → Rea p ⟨e, ρ⟩



/-
Adequation / Soundness / Fundamental property
-/

def adLookup : (v : Var a γ) → ReaEnv p γ ρ → Rea p (lookup v ρ)
  | Var.zero,   ReaEnv.cons ri _  => ri
  | Var.succ v, ReaEnv.cons _  re => adLookup v re

def ad (p : J → Sort u) (pj : p j) : (e : Exp j δ γ) → Rea' p e
  | Exp.C.step eo v,   _, re => ReaC.step (adLookup v re (ReaOs.cons (ad p pj eo re) ReaOs.nil))
  | Exp.C.halt _,      _, _  => ReaC.halt _ pj
  | Exp.I.stable ec,   _, re => fun | ReaOs.nil =>                                    by unfold apply; exact ad p pj ec  re
  | Exp.I.not ei,      _, re => fun | ReaOs.cons (co := ⟨Exp.O.not _,   _⟩) ro ros => by unfold apply; exact ad p pj ei  (ReaEnv.cons (fun | ReaOs.cons ro' ReaOs.nil => ro ro') re) ros
  | Exp.I.and ei,      _, re => fun | ReaOs.cons (co := ⟨Exp.O.and _ _, _⟩) ro ros => by unfold apply; exact ad p pj ei  re                                                          (ReaOs.cons ro.1 (ReaOs.cons ro.2 ros))
  | Exp.I.true ei,     _, re => fun | ReaOs.cons (co := ⟨Exp.O.true,    _⟩) _  ros => by unfold apply; exact ad p pj ei  re                                                          ros
  | Exp.I.or ei₁ ei₂,  _, re => fun | ReaOs.cons (co := ⟨Exp.O.or₁ _,   _⟩) ro ros => by unfold apply; exact ad p pj ei₁ re                                                          (ReaOs.cons ro ros)
                                    | ReaOs.cons (co := ⟨Exp.O.or₂ _,   _⟩) ro ros => by unfold apply; exact ad p pj ei₂ re                                                          (ReaOs.cons ro ros)
  | Exp.I.false,       _, _  => fun ro => nomatch ro
  | Exp.O.not ei,      _, re => fun ro' => ad p pj ei re (ReaOs.cons ro' ReaOs.nil)
  | Exp.O.and eo₁ eo₂, _, re => (ad p pj eo₁ re, ad p pj eo₂ re)
  | Exp.O.true,        _, _  => PUnit.unit
  | Exp.O.or₁ eo,      _, re => ad p pj eo re
  | Exp.O.or₂ eo,      _, re => ad p pj eo re



/-
Lemmas
-/

def halt : ReaC (J := J) p cc → J
  | ReaC.halt j _ => j
  | ReaC.step rc  => halt rc

def haltP : (rc : ReaC p cc) → p (halt rc)
  | ReaC.halt _ pj => pj
  | ReaC.step rc   => haltP rc

def haltEq : {rc : ReaC p cc} → {rc' : ReaC p' cc} → halt rc = halt rc'
  | ReaC.halt _ _, ReaC.halt _ _ => rfl
  | ReaC.step rc,  ReaC.step rc' => haltEq (rc := rc) (rc' := rc')



/-
Games and strategies
-/

inductive Player : Type
  | proponent : Player
  | opponent  : Player

def Strategy (a : Typ) : Player → Type
  | Player.proponent => Exp Player.proponent C [a]
  | Player.opponent  => Exp Player.opponent (I [a]) []

def loser {a : Typ} (strategies : (j : Player) → Strategy a j) : Player :=
  let ei := strategies Player.opponent
  let ec := strategies Player.proponent
  let ρ  := Env.cons (Clo.mk ei Env.nil) Env.nil
  let cc := Clo.mk ec ρ
  let p  := fun _ => True
  let re : ReaEnv p [a] ρ := ReaEnv.cons (ad p True.intro ei ReaEnv.nil) ReaEnv.nil
  let rc : ReaC p cc      := ad p True.intro ec re
  halt rc

def Winning : {j : Player} → Strategy a j → Type 2
  | Player.proponent => Rea' (· ≠ Player.proponent)
  | Player.opponent  => Rea' (· ≠ Player.opponent)

theorem win {j : Player} (strategies : (j : Player) → Strategy a j) (w : Winning (strategies j)) : loser strategies ≠ j :=
  let ei := strategies Player.opponent
  let ec := strategies Player.proponent
  let ρ  := Env.cons (Clo.mk ei Env.nil) Env.nil
  let cc := Clo.mk ec ρ
  match j with
    | Player.proponent => by
      let p  := (· ≠ Player.proponent)
      let re : ReaEnv p [a] ρ := ReaEnv.cons (ad p Player.noConfusion ei ReaEnv.nil) ReaEnv.nil
      let rc : ReaC p cc      := w re
      unfold loser
      exact haltEq ▸ haltP rc
    | Player.opponent => by
      let p  := (· ≠ Player.opponent)
      let re : ReaEnv p [a] ρ := ReaEnv.cons (w ReaEnv.nil) ReaEnv.nil
      let rc : ReaC p cc      := ad p Player.noConfusion ec re
      unfold loser
      exact haltEq ▸ haltP rc
