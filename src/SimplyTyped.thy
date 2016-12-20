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
lift_definition prm :: "'a prm \<Rightarrow> 'a trm \<Rightarrow> 'a trm" (infixr "\<cdot>" 150) is ptrm_apply_prm
  using ptrm_alpha_equiv_prm.

lemma var_not_app:
  shows "Var x \<noteq> App A B"
proof(transfer)
  fix x :: 'a and A B
  show "\<not>PVar x =a PApp A B"
  proof(rule classical)
    assume "\<not>\<not>PVar x =a PApp A B"
    hence False using varE ptrm.distinct(1) by fastforce
    thus ?thesis by blast
  qed
qed

lemma var_not_fn:
  shows "Var x \<noteq> Fn y T A"
proof(transfer)
  fix x y :: 'a and T A
  show "\<not>PVar x =a PFn y T A"
  proof(rule classical)
    assume "\<not>\<not>PVar x =a PFn y T A" 
    hence False using varE ptrm.distinct(2) by fastforce
    thus ?thesis by blast
  qed
qed

lemma app_not_fn:
  shows "App A B \<noteq> Fn y T X"
proof(transfer)
  fix y :: 'a and A B T X
  show "\<not>PApp A B =a PFn y T X"
  proof(rule classical)
    assume "\<not>\<not>PApp A B =a PFn y T X"
    hence False using appE ptrm.distinct(5) by auto
    thus ?thesis by blast
  qed
qed

lemma trm_simp:
  shows
    "Var x = Var y \<Longrightarrow> x = y"
    "App A B = App C D \<Longrightarrow> A = C"
    "App A B = App C D \<Longrightarrow> B = D"
    "Fn x T A = Fn y S B \<Longrightarrow>
      (x = y \<and> T = S \<and> A = B) \<or> (x \<noteq> y \<and> T = S \<and> x \<notin> fvs B \<and> A = [x \<leftrightarrow> y] \<cdot> B)"
  apply (transfer, insert ptrm.inject(1) varE, fastforce)[]
  apply (transfer, insert ptrm.inject(2) appE, auto)[]
  apply (transfer, insert ptrm.inject(2) appE, auto)[]
  apply (transfer', smt ptrm.inject(3) fnE)[]
done

lemma trm_prm_simp:
  shows
    "\<pi> \<cdot> Var x = Var (\<pi> $ x)"
    "\<pi> \<cdot> App A B = App (\<pi> \<cdot> A) (\<pi> \<cdot> B)"
    "\<pi> \<cdot> Fn x T A = Fn (\<pi> $ x) T (\<pi> \<cdot> A)"
  apply (transfer', auto simp add: ptrm_alpha_equiv_reflexive)
  apply (transfer, auto simp add: ptrm_alpha_equiv_reflexive)
  apply (transfer, auto simp add: ptrm_alpha_equiv_reflexive)
done

lemma fvs_finite:
  shows "finite (fvs M)"
by(transfer, metis ptrm_fvs_finite)

lemma fvs_simp:
  shows
    "fvs (Var x) = {x}"
    "fvs (App A B) = fvs A \<union> fvs B"
    "fvs (Fn x T A) = fvs A - {x}"
by((transfer, simp)+)

lemma var_prm_action:
  shows "[a \<leftrightarrow> b] \<cdot> Var a = Var b"
by(transfer', simp add: prm_unit_action ptrm_alpha_equiv.intros)

lemma var_prm_inaction:
  assumes "a \<noteq> x" "b \<noteq> x"
  shows "[a \<leftrightarrow> b] \<cdot> Var x = Var x"
using assms by(transfer', simp add: prm_unit_inaction ptrm_alpha_equiv.intros)

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

lemma (in fresh) trm_strong_induct:
  fixes P :: "'a set \<Rightarrow> 'a trm \<Rightarrow> bool"
  assumes
    "\<And>c x. finite c \<Longrightarrow> P c (Var x)"
    "\<And>c A B. \<lbrakk>finite c; \<And>c'. finite c' \<Longrightarrow> P c' A; \<And>c'. finite c' \<Longrightarrow> P c' B\<rbrakk> \<Longrightarrow> P c (App A B)"
    "\<And>c x T A. \<lbrakk>finite c; x \<notin> c; \<And>c'. finite c' \<Longrightarrow> P c' A\<rbrakk> \<Longrightarrow> P c (Fn x T A)"
  shows "\<And>c. finite c \<Longrightarrow> P c M"
sorry

lemma trm_prm_id:
  shows "\<epsilon> \<cdot> M = M"
by(induction M rule: trm_induct, auto simp add: trm_prm_simp prm_apply_id)

inductive typing :: "'a typing_ctx \<Rightarrow> 'a trm \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
  tvar: "\<Gamma> x = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<tau>"
| tapp: "\<lbrakk>\<Gamma> \<turnstile> f : TArr \<tau> \<sigma>; \<Gamma> \<turnstile> x : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App f x : \<sigma>"
| tfn:  "\<Gamma>(x \<mapsto> \<tau>) \<turnstile> A : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> Fn x \<tau> A : TArr \<tau> \<sigma>"

lemma typing_prm:
  assumes "\<Gamma> \<turnstile> M : \<tau>" "\<And>x. x \<in> fvs M \<Longrightarrow> \<Gamma> x = \<Delta> (\<pi> $ x)"
  shows "\<Delta> \<turnstile> \<pi> \<cdot> M : \<tau>"
using assms proof(induction arbitrary: \<Delta> rule: typing.induct)
  case (tvar \<Gamma> x \<tau>)
    thus ?case using typing.tvar trm_prm_simp(1) fvs_simp(1) singletonI by metis
  next
  case (tapp \<Gamma> A \<tau> \<sigma> B)
    thus ?case using typing.tapp trm_prm_simp(2) fvs_simp(2) UnCI by metis
  next
  case (tfn \<Gamma> x \<tau> A \<sigma>)
    thus ?case using typing.tfn trm_prm_simp(3) fvs_simp(3)
      using fun_upd_apply prm_apply_unequal Diff_empty Diff_insert0 insert_Diff insert_iff
      by smt
  next
qed

lemma typing_swp:
  assumes "\<Gamma>(a \<mapsto> \<sigma>) \<turnstile> M : \<tau>" "b \<notin> fvs M"
  shows "\<Gamma>(b \<mapsto> \<sigma>) \<turnstile> [a \<leftrightarrow> b] \<cdot> M : \<tau>"
proof -
  (* hack to make induction work sensibly *)
  obtain \<Delta> where \<Delta>: "\<Delta> = \<Gamma>(a \<mapsto> \<sigma>)" by auto
  hence "\<Delta> \<turnstile> M : \<tau>" using assms by auto
  thus ?thesis using \<Delta> `b \<notin> fvs M`
  proof(induction arbitrary: \<Gamma> \<sigma> a b rule: typing.induct)
    case (tvar \<Delta> x \<tau>)
      have "fvs (Var x) = {x}" using fvs_simp by fastforce
      hence "x \<noteq> b" using tvar.prems by auto
      consider "x = a" | "x \<noteq> a" by auto
      thus ?case proof(cases)
        case 1
          hence "\<tau> = \<sigma>" using tvar by simp
          thus ?thesis using `x = a` typing.tvar var_prm_action fun_upd_same by metis
        next
        case 2
          thus ?thesis
            using tvar var_prm_inaction `x \<noteq> b` typing.tvar map_upd_Some_unfold
            by (metis (no_types, lifting))
        next
      qed
    next
    case (tapp \<Delta> A \<tau>' \<tau> B)
      have "b \<notin> fvs A" and "b \<notin> fvs B"
        using `b \<notin> fvs (App A B)` fvs_simp(2) UnCI by metis+
      hence "\<Gamma>(b \<mapsto> \<sigma>) \<turnstile> [a \<leftrightarrow> b] \<cdot> A : TArr \<tau>' \<tau>" and "\<Gamma>(b \<mapsto> \<sigma>) \<turnstile> [a \<leftrightarrow> b] \<cdot> B : \<tau>'"
        using tapp.IH tapp.prems by metis+
      thus ?case using trm_prm_simp typing.tapp by smt
    next
    case (tfn \<Delta> x T A \<tau>)
      from this consider "b = x" | "b \<noteq> x \<and> b \<notin> fvs A" using fvs_simp(3)
        using DiffI singletonD by fastforce
      thus ?case proof(cases)
        case 1
          consider "a = x" | "a \<noteq> x" by auto
          thus ?thesis proof(cases)
            case 1
              hence *: "[a \<leftrightarrow> b] \<cdot> Fn x T A = Fn x T A"
                using prm_unit_equal_id trm_prm_id `b = x` by metis
              have "\<Delta>(x \<mapsto> T) = \<Gamma>(b \<mapsto> T)" using `a = x` `b = x` tfn.prems(1) by auto
              thus ?thesis using tfn.hyps * typing.tfn fun_upd_upd `a = x` `b = x`
                by metis
            next
            case 2
              thus ?thesis
                using tfn typing_prm fun_upd_apply prm_unit_action prm_unit_inaction typing.tfn
                by smt
            next
          qed
        next
        case 2
          hence "b \<noteq> x" and "b \<notin> fvs A" by auto
          consider "a = x" | "a \<noteq> x" by auto
          thus ?thesis proof(cases)
            case 1
              hence *: "[a \<leftrightarrow> b] \<cdot> Fn x T A = Fn b T ([a \<leftrightarrow> b] \<cdot> A)"
                using trm_prm_simp(3) prm_unit_action by metis
              have "\<Delta>(x \<mapsto> T) = \<Gamma>(a \<mapsto> T)" using `a = x` tfn.prems(1) by auto
              hence "\<Gamma>(b \<mapsto> T) \<turnstile> [a \<leftrightarrow> b] \<cdot> A : \<tau>" using tfn.IH `b \<notin> fvs A` by metis
              thus ?thesis using typing.tfn * fun_upd_upd by metis
            next
            case 2
              hence *: "[a \<leftrightarrow> b] \<cdot> Fn x T A = Fn x T ([a \<leftrightarrow> b] \<cdot> A)"
                using trm_prm_simp(3) prm_unit_inaction `b \<noteq> x` by metis
              have "\<Delta>(x \<mapsto> T) = \<Gamma>(x \<mapsto> T)(a \<mapsto> \<sigma>)" using tfn.prems(1) `a \<noteq> x` by auto
              hence "\<Gamma>(x \<mapsto> T)(b \<mapsto> \<sigma>) \<turnstile> [a \<leftrightarrow> b] \<cdot> A : \<tau>" using tfn.IH `b \<notin> fvs A` by metis
              hence "\<Gamma>(b \<mapsto> \<sigma>)(x \<mapsto> T) \<turnstile> [a \<leftrightarrow> b] \<cdot> A : \<tau>" using `b \<noteq> x`
                by (simp add: fun_upd_twist)
              thus ?thesis using typing.tfn * by metis
            next
          qed
        next
      qed
    next
  qed
qed

lemma typing_varE:
  assumes "\<Gamma> \<turnstile> Var x : \<tau>"
  shows "\<Gamma> x = Some \<tau>"
using assms by(cases, metis trm_simp(1), auto simp add: var_not_app var_not_fn)

lemma typing_appE:
  assumes "\<Gamma> \<turnstile> App A B : \<sigma>"
  shows "\<exists>\<tau>. \<Gamma> \<turnstile> A : TArr \<tau> \<sigma> \<and> \<Gamma> \<turnstile> B : \<tau>"
using assms by(cases, metis var_not_app, metis trm_simp(2) trm_simp(3), metis app_not_fn)

lemma typing_fnE:
  assumes "\<Gamma> \<turnstile> Fn x T A : \<theta>"
  shows "\<exists>\<sigma>. \<theta> = TArr T \<sigma> \<and> \<Gamma>(x \<mapsto> T) \<turnstile> A : \<sigma>"
using assms proof(cases, metis var_not_fn, metis app_not_fn)
  case (tfn y S B \<sigma>)
    from this consider
      "x = y \<and> T = S \<and> A = B" | "x \<noteq> y \<and> T = S \<and> x \<notin> fvs B \<and> A = [x \<leftrightarrow> y] \<cdot> B"
      using trm_simp(4) by metis
    thus ?thesis proof(cases)
      case 1
        thus ?thesis using tfn by metis
      next
      case 2
        thus ?thesis using tfn typing_swp prm_unit_commutes by metis
      next
    qed
  next
qed

lift_definition infer_type :: "'a typing_ctx \<Rightarrow> 'a trm \<Rightarrow> type option" is ptrm_infer_type
proof(transfer)
  fix \<Gamma> :: "'a typing_ctx" and X Y :: "'a ptrm"
  assume "X =a Y"
  thus "ptrm_infer_type \<Gamma> X = ptrm_infer_type \<Gamma> Y" using ptrm_infer_type_alpha_equiv by auto
qed

theorem infer_type_valid:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
  shows "infer_type \<Gamma> M = Some \<tau>"
using assms proof(induction arbitrary: \<Gamma> \<tau> rule: trm_induct)
  case (1 x)
    hence "\<Gamma> x = Some \<tau>" using typing_varE by metis
    thus ?case by(transfer, simp)
  next
  case (2 A B)
    from this obtain \<sigma> where "\<Gamma> \<turnstile> A : TArr \<sigma> \<tau>" "\<Gamma> \<turnstile> B : \<sigma>" using typing_appE by metis
    hence "infer_type \<Gamma> A = Some (TArr \<sigma> \<tau>)" and "infer_type \<Gamma> B = Some \<sigma>" using "2.IH" by auto
    thus ?case by(transfer, simp)
  next
  case (3 x T A \<Gamma> S)
    from this obtain \<sigma> where S: "S = TArr T \<sigma>" and "\<Gamma>(x \<mapsto> T) \<turnstile> A : \<sigma>" using typing_fnE by metis
    hence "infer_type (\<Gamma>(x \<mapsto> T)) A = Some \<sigma>" using "3.IH" by auto
    thus ?case using S by(transfer, simp)
  next
qed

end
