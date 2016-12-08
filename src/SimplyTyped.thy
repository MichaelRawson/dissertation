theory SimplyTyped
imports Main Permutation Fresh PreSimplyTyped
begin

quotient_type 'a trm = "'a ptrm" / ptrm_alpha_equiv
proof(rule equivpI)
  show "reflp  ptrm_alpha_equiv" using ptrm_alpha_equiv_reflp.
  show "symp   ptrm_alpha_equiv" using ptrm_alpha_equiv_symp.
  show "transp ptrm_alpha_equiv" using ptrm_alpha_equiv_transp.
qed

lift_definition Var :: "'a \<Rightarrow> 'a trm" is PVar.
lift_definition App :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> 'a trm" is PApp using ptrm_alpha_equiv.app.
lift_definition Fn  :: "'a \<Rightarrow> type \<Rightarrow> 'a trm \<Rightarrow> 'a trm" is PFn using ptrm_alpha_equiv.fn1.
lift_definition fvs :: "'a trm \<Rightarrow> 'a set" is ptrm_fvs using ptrm_alpha_equiv_fvs.

lemma trm_induct:
  fixes P :: "'a trm \<Rightarrow> bool"
  assumes
    "\<And>x. P (Var x)"
    "\<And>A B. \<lbrakk>P A; P B\<rbrakk> \<Longrightarrow> P (App A B)"
    "\<And>x T A. P A \<Longrightarrow> P (Fn x T A)"
  shows "P M"
proof -
  have "\<And>X. P (abs_trm X)"
  proof(rule ptrm.induct)
    show "\<And>X x. P (abs_trm (PVar x))"
      using assms(1) Var.abs_eq by metis
    show "\<And>X A B. \<lbrakk>P (abs_trm A); P (abs_trm B)\<rbrakk> \<Longrightarrow> P (abs_trm (PApp A B))"
      using assms(2) App.abs_eq by metis
    show "\<And>X x T A. P (abs_trm A) \<Longrightarrow> P (abs_trm (PFn x T A))"
      using assms(3) Fn.abs_eq by metis
  qed
  thus ?thesis using trm.abs_induct by auto
qed

lemma trm_strong_induct:
  fixes P :: "'a set \<Rightarrow> 'a trm \<Rightarrow> bool"
  assumes
    "\<And>c x. P c (Var x)"
    "\<And>c A B. \<lbrakk>\<And>c'. P c' A; \<And>c'. P c' B\<rbrakk> \<Longrightarrow> P c (App A B)"
    "\<And>c x T A. \<lbrakk>x \<notin> c; \<And>c'. P c' A\<rbrakk> \<Longrightarrow> P c (Fn x T A)"
  shows "\<And>c. P c M"
proof -
  have "\<And>c X. P c (abs_trm X)"
  proof(rule ptrm.induct)
    show "\<And>c X x. P c (abs_trm (PVar x))"
      using assms(1) Var.abs_eq by metis
    show "\<And>c X A B. \<lbrakk>P c (abs_trm A); P c (abs_trm B)\<rbrakk> \<Longrightarrow> P c (abs_trm (PApp A B))"
    proof -
      fix c X A B
      assume "P c (abs_trm A)"
      hence "\<And>c'. P c' (abs_trm A)" 
qed

type_synonym 'a typing_ctx = "'a \<rightharpoonup> type"

fun ptrm_subst :: "'a ptrm \<Rightarrow> 'a \<Rightarrow> 'a ptrm \<Rightarrow> 'a ptrm" where
  "ptrm_subst (PVar x)    y M = (if x = y then M else PVar x)"
| "ptrm_subst (PApp A B)  y M = PApp (ptrm_subst A y M) (ptrm_subst B y M)"
| "ptrm_subst (PFn x T A) y M = PFn x T (if x = y then A else ptrm_subst A y M)"

lemma ptrm_subst_fresh:
  assumes "a \<notin> ptrm_fvs X"
  shows "a \<notin> ptrm_fvs (ptrm_subst X a Y)"
using assms by(induction X, auto)

lift_definition trm_subst :: "'a trm \<Rightarrow> 'a \<Rightarrow> 'a trm \<Rightarrow> 'a trm" ("_[_ := _]") is ptrm_subst
proof -
  fix y :: 'a
  fix A B C D :: "'a ptrm"
  assume "A =a B" "C =a D"
  thus "ptrm_subst A y C =a ptrm_subst B y D"
  proof(induction rule: ptrm_alpha_equiv.induct)
    case (var x)
      thus ?case by(cases "x = y", auto simp add: ptrm_alpha_equiv.var)
    next
    case (app E F G H)
      thus ?case by(simp add: ptrm_alpha_equiv.app)
    next
    case (fn1 A B x T)
      thus ?case by(simp add: ptrm_alpha_equiv.fn1)
    next
    case (fn2 a b A B T)
      consider "y = a" | "y = b" | "y \<noteq> a \<and> y \<noteq> b" by auto
      thus ?case proof(cases)
        case 1
          hence *:
            "ptrm_subst (PFn a T A) y C = PFn a T A"
            "ptrm_subst (PFn b T B) y D = PFn b T (ptrm_subst B a D)"
          using `a \<noteq> b` by auto
          have "a \<notin> ptrm_fvs (ptrm_subst B a D)" using `a \<notin> ptrm_fvs B` ptrm_subst_fresh by metis
          moreover have "A =a [a \<leftrightarrow> b] \<cdot> (ptrm_subst B a D)" sorry
          ultimately show ?thesis using `a \<noteq> b` * ptrm_alpha_equiv.fn2 by metis
        next
          
inductive typing :: "'a typing_ctx \<Rightarrow> 'a trm \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
  tvar: "\<Gamma> x = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<tau>"
| tapp: "\<lbrakk>\<Gamma> \<turnstile> f : TArr \<tau> \<sigma>; \<Gamma> \<turnstile> x : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App f x : \<sigma>"
| tfn:  "\<Gamma>(x \<mapsto> \<tau>) \<turnstile> A : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> Fn x \<tau> A : TArr \<tau> \<sigma>"
end
