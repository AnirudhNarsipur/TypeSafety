import Lean.Data.HashMap

inductive Exp
| var : String -> Exp
| true : Exp
| false : Exp
| ite : Exp → Exp → Exp → Exp
| lam : String →  Exp → Exp
| app : Exp → Exp → Exp
deriving Inhabited, BEq, Repr

inductive Typ
| bool
| func : Typ → Typ → Typ


def is_val : Exp → Prop
| Exp.true => true
| Exp.false => true
| Exp.lam _ _=> true
| _ => false


def Context : Type := String → Typ

def Env :Type := String → Exp

def emptyContext :Context := fun _ => Typ.bool
-- def emptyEvalContext : Env := fun _ => Exp.false
-- def update (g : Context) (s : String ) (v : Typ) : Context :=  fun s1 => if s1 == s then v else (g s1)

-- #check ∀ g  s v,fun s1 => if s1 == s then v else (g s1)
theorem tr : is_val Exp.true := by  constructor
theorem trf: is_val Exp.false := by  constructor


-- #check  ∀ x : Nat , x + 1 -- (update emptyEvalContext "1" (Exp.true))

inductive hasTyp : Context →  Exp -> Typ → Prop where
| t_tru  : hasTyp Γ (Exp.true) Typ.bool
| t_fls  :  hasTyp Γ (Exp.false) Typ.bool
| t_var  : ∀  x τ, Γ x =  τ → hasTyp Γ (Exp.var x) τ
| t_ite : ∀  e1 e2 e3 τ, hasTyp Γ e1 Typ.bool → hasTyp Γ e2 τ → hasTyp Γ e3 τ → hasTyp Γ (Exp.ite e1 e2 e3) τ
| t_lam : ∀ x e τ2, Γ x =  τ1 → hasTyp Γ e τ2 →   hasTyp Γ (Exp.lam x e) (Typ.func τ1 τ2)
| t_app : ∀ τ1 τ2 e1 e2, hasTyp Γ e1 (Typ.func τ1 τ2) → hasTyp Γ e2 (τ1) → hasTyp Γ (Exp.app e1 e2) τ2


def T : Type := (Env × Exp)

def subst (v : Exp) (hv : is_val v) (x : String)  : Exp → Exp
| Exp.ite e1 e2 e3 => Exp.ite (subst v hv x e1) (subst v hv x e2) (subst v hv x e3)
| Exp.app e1 e2 => Exp.app (subst v hv x e1) (subst v hv x e2)
| Exp.true => Exp.true
| Exp.false => Exp.false
| Exp.var y => if x == y then v else Exp.var y
| Exp.lam y e => if x == y then Exp.lam y e else Exp.lam y (subst v hv x e)



inductive SmallStep :  Exp → Exp  → Prop where
| if_true (e1 e2  ) :  SmallStep  (Exp.ite Exp.true e1 e2)   e1
| if_false (e1 e2 ) : SmallStep  (Exp.ite Exp.false e1 e2 ) e2
| e_app (e2 v1 x ) (hv : is_val v1):    SmallStep  (Exp.app (Exp.lam x e2) v1)  (subst v1 hv x e2)
| e_step1 ( e1 e1' e2 e3 ): SmallStep e1 e1' →  SmallStep  (Exp.ite e1 e2 e3 )  (Exp.ite e1' e2 e3 )
| e_step2 (e1 e1' e2 ): SmallStep e1 e1' →  SmallStep  (Exp.app e1 e2  )  (Exp.app e1' e2 )
| e_step3 (e1 e2' e2 ):   SmallStep e2 e2' → is_val e1 →  SmallStep (Exp.app e1 e2) ( (Exp.app e1 e2' ))

-- def tstCont := emptyEvalContext
-- #check ∀ v , SmallStep (tstCont, (Exp.ite Exp.true v v)) (tstCont, v)


inductive RTC {α : Type } (R : α → α → Prop) (a : α ): α → Prop where
| base : RTC R a a
| trans : ∀ b c,  RTC R a b →  R b c →  RTC R a c


infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

#check Env
#check RTC SmallStep

def reduc (e : Exp) : Prop := ∃ v , is_val v ∧  e ⇒* v

postfix:100 " ⇓ " => reduc

inductive  Norm: Exp → Typ  →  Prop where
| Nbool (e) : hasTyp emptyContext e Typ.bool →  e ⇓ →  Norm e Typ.bool
| Nfunc (e t1 t2 e') : hasTyp emptyContext e (Typ.func t1 t2) → e ⇓ →  Norm e' t1 → Norm (Exp.app e e' ) t2 → Norm e (Typ.func t1 t2)


theorem partB (e : Exp) (t : Typ) : Norm e t → e ⇓ := by
  intro h
  cases h
  . assumption
  . assumption
  done

theorem partA (e : Exp) (t : Typ) : hasTyp emptyContext e t → Norm e t := sorry



theorem safe (e : Exp ) (t : Typ) :  hasTyp emptyContext e t → e ⇓ := by
intro h
apply partB e t
apply partA
assumption
done
