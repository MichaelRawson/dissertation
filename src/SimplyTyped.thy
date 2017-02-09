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
lift_definition depth :: "'a trm \<Rightarrow> nat" is size using ptrm_size_alpha_equiv.

lemma depth_prm:
  shows "depth A = depth (\<pi> \<cdot> A)"
by(transfer, metis ptrm_size_prm)

lemma depth_app:
  shows "depth A < depth (App A B)" "depth B < depth (App A B)"
by(transfer, auto)+

lemma depth_fn:
  shows "depth A < depth (Fn x T A)"
by(transfer, auto)

lemma var_not_app:
  shows "Var x \<noteq> App A B"
proof(transfer)
  fix x :: 'a and A B
  show "\<not>PVar x \<approx> PApp A B"
  proof(rule classical)
    assume "\<not>\<not>PVar x \<approx> PApp A B"
    hence False using varE ptrm.distinct(1) by fastforce
    thus ?thesis by blast
  qed
qed

lemma var_not_fn:
  shows "Var x \<noteq> Fn y T A"
proof(transfer)
  fix x y :: 'a and T A
  show "\<not>PVar x \<approx> PFn y T A"
  proof(rule classical)
    assume "\<not>\<not>PVar x \<approx> PFn y T A" 
    hence False using varE ptrm.distinct(2) by fastforce
    thus ?thesis by blast
  qed
qed

lemma app_not_fn:
  shows "App A B \<noteq> Fn y T X"
proof(transfer)
  fix y :: 'a and A B T X
  show "\<not>PApp A B \<approx> PFn y T X"
  proof(rule classical)
    assume "\<not>\<not>PApp A B \<approx> PFn y T X"
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

lemma fn_eq:
  assumes "x \<noteq> y" "x \<notin> fvs B" "A = [x \<leftrightarrow> y] \<cdot> B"
  shows "Fn x T A = Fn y T B"
using assms by(transfer', metis ptrm_alpha_equiv.fn2)

lemma trm_prm_simp:
  shows
    "\<pi> \<cdot> Var x = Var (\<pi> $ x)"
    "\<pi> \<cdot> App A B = App (\<pi> \<cdot> A) (\<pi> \<cdot> B)"
    "\<pi> \<cdot> Fn x T A = Fn (\<pi> $ x) T (\<pi> \<cdot> A)"
  apply (transfer', auto simp add: ptrm_alpha_equiv_reflexive)
  apply (transfer, auto simp add: ptrm_alpha_equiv_reflexive)
  apply (transfer, auto simp add: ptrm_alpha_equiv_reflexive)
done

lemma trm_prm_apply_compose:
  shows "\<pi> \<cdot> \<sigma> \<cdot> A = (\<pi> \<diamondop> \<sigma>) \<cdot> A"
by(transfer', metis ptrm_prm_apply_compose ptrm_alpha_equiv_reflexive)

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

lemma trm_prm_apply_id:
  shows "\<epsilon> \<cdot> M = M"
by(transfer', auto simp add: ptrm_prm_apply_id)

lemma trm_prm_agreement_equiv:
  assumes "\<And>a. a \<in> ds \<pi> \<sigma> \<Longrightarrow> a \<notin> fvs M"
  shows "\<pi> \<cdot> M = \<sigma> \<cdot> M"
using assms by(transfer, metis ptrm_prm_agreement_equiv)

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

lemma trm_cases:
  assumes
    "\<And>x. M = Var x \<Longrightarrow> P M"
    "\<And>A B. M = App A B \<Longrightarrow> P M"
    "\<And>x T A. M = Fn x T A \<Longrightarrow> P M"
  shows "P M"
using assms by(induction rule: trm_induct, auto)

lemma trm_depth_induct:
  assumes
    "\<And>x. P (Var x)"
    "\<And>A B. \<lbrakk>\<And>K. depth K < depth (App A B) \<Longrightarrow> P K\<rbrakk> \<Longrightarrow> P (App A B)"
    "\<And>M x T A. (\<And>K. depth K < depth (Fn x T A) \<Longrightarrow> P K) \<Longrightarrow> P (Fn x T A)"
  shows "P M"
proof(induction "depth M" arbitrary: M rule: less_induct)
  fix M :: "'a trm"
  assume IH: "depth K < depth M \<Longrightarrow> P K" for K
  hence
    "\<And>x.     M = Var x \<Longrightarrow>    P M"
    "\<And>A B.   M = App A B \<Longrightarrow>  P M"
    "\<And>x T A. M = Fn x T A \<Longrightarrow> P M"
    using assms by blast+
  thus "P M" using trm_cases by metis
qed

context fresh begin

lemma trm_strong_induct:
  fixes P :: "'a set \<Rightarrow> 'a trm \<Rightarrow> bool"
  assumes
    "\<And>x. P S (Var x)"
    "\<And>A B. \<lbrakk>P S A; P S B\<rbrakk> \<Longrightarrow> P S (App A B)"
    "\<And>x T. x \<notin> S \<Longrightarrow> (\<And>A. P S A \<Longrightarrow> P S (Fn x T A))"
    "finite S"
  shows "P S M"
proof -
  have "\<And>\<pi>. P S (\<pi> \<cdot> M)"
  proof(induction M rule: trm_induct)
    case (1 x)
      thus ?case using assms(1) trm_prm_simp(1) by metis
    next
    case (2 A B)
      thus ?case using assms(2) trm_prm_simp(2) by metis
    next
    case (3 x T A)
      have "finite S" "finite (fvs (\<pi> \<cdot> A))" "finite {\<pi> $ x}"
        using assms(4) fvs_finite by auto
      hence "finite (S \<union> fvs (\<pi> \<cdot> A) \<union> {\<pi> $ x})" by auto
      
      obtain y where "y = fresh_in (S \<union> fvs (\<pi> \<cdot> A) \<union> {\<pi> $ x})" by auto
      hence "y \<notin> S \<union> fvs (\<pi> \<cdot> A) \<union> {\<pi> $ x}" using fresh_axioms unfolding class.fresh_def
        using `finite (S \<union> fvs (\<pi> \<cdot> A) \<union> {\<pi> $ x})` by metis
      hence "y \<noteq> \<pi> $ x" "y \<notin> fvs (\<pi> \<cdot> A)" "y \<notin> S" by auto
      hence *: "\<And>A. P S A \<Longrightarrow> P S (Fn y T A)" using assms(3) by metis
  
      have "P S (([y \<leftrightarrow> \<pi> $ x] \<diamondop> \<pi>) \<cdot> A)" using 3 by metis
      moreover hence "P S (Fn y T (([y \<leftrightarrow> \<pi> $ x] \<diamondop> \<pi>) \<cdot> A))" using * by metis
      moreover have "(Fn y T (([y \<leftrightarrow> \<pi> $ x] \<diamondop> \<pi>) \<cdot> A)) = Fn (\<pi> $ x) T (\<pi> \<cdot> A)"
        using trm_prm_apply_compose fn_eq `y \<noteq> \<pi> $ x` `y \<notin> fvs (\<pi> \<cdot> A)` by metis
      ultimately show ?case using trm_prm_simp(3) by metis
    next
  qed
  hence "P S (\<epsilon> \<cdot> M)" by metis
  thus "P S M" using trm_prm_apply_id by metis
qed

lemma trm_strong_cases:
  fixes P :: "'a set \<Rightarrow> 'a trm \<Rightarrow> bool"
  assumes
    "\<And>x.     M = Var x    \<Longrightarrow> P S M"
    "\<And>A B.   M = App A B  \<Longrightarrow> P S (App A B)"
    "\<And>x T A. M = Fn x T A \<Longrightarrow> x \<notin> S \<Longrightarrow> P S (Fn x T A)"
    "finite S"
  shows "P S M"
using assms by(induction S M rule: trm_strong_induct, metis+)

lemma trm_strong_depth_induct:
  fixes P :: "'a set \<Rightarrow> 'a trm \<Rightarrow> bool"
  assumes
    "\<And>x. P S (Var x)"
    "\<And>A B. \<lbrakk>\<And>K. depth K < depth (App A B) \<Longrightarrow> P S K\<rbrakk> \<Longrightarrow> P S (App A B)"
    "\<And>x T. x \<notin> S \<Longrightarrow> (\<And>A. (\<And>K. depth K < depth (Fn x T A) \<Longrightarrow> P S K) \<Longrightarrow> P S (Fn x T A))"
    "finite S"
  shows "P S M"
proof(induction "depth M" arbitrary: M rule: less_induct)
  fix M :: "'a trm"
  assume IH: "depth K < depth M \<Longrightarrow> P S K" for K
  hence
    "\<And>x.     M = Var x    \<Longrightarrow> P S M"
    "\<And>A B.   M = App A B  \<Longrightarrow> P S (App A B)"
    "\<And>x T A. M = Fn x T A \<Longrightarrow> x \<notin> S \<Longrightarrow> P S (Fn x T A)"
    "finite S"
    using assms IH by metis+
  thus "P S M" using trm_strong_cases by metis
qed

lemma trm_prm_fvs:
  shows "fvs (\<pi> \<cdot> M) = \<pi> {$} fvs M"
by(transfer, metis ptrm_prm_fvs)

inductive typing :: "'a typing_ctx \<Rightarrow> 'a trm \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
  tvar: "\<Gamma> x = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<tau>"
| tapp: "\<lbrakk>\<Gamma> \<turnstile> f : (TArr \<tau> \<sigma>); \<Gamma> \<turnstile> x : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App f x : \<sigma>"
| tfn:  "\<Gamma>(x \<mapsto> \<tau>) \<turnstile> A : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> Fn x \<tau> A : (TArr \<tau> \<sigma>)"

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
      hence "\<Gamma>(b \<mapsto> \<sigma>) \<turnstile> [a \<leftrightarrow> b] \<cdot> A : (TArr \<tau>' \<tau>)" and "\<Gamma>(b \<mapsto> \<sigma>) \<turnstile> [a \<leftrightarrow> b] \<cdot> B : \<tau>'"
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
                using prm_unit_equal_id trm_prm_apply_id `b = x` by metis
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
  shows "\<exists>\<tau>. (\<Gamma> \<turnstile> A : (TArr \<tau> \<sigma>)) \<and> (\<Gamma> \<turnstile> B : \<tau>)"
using assms by(cases, metis var_not_app, metis trm_simp(2) trm_simp(3), metis app_not_fn)

lemma typing_fnE:
  assumes "\<Gamma> \<turnstile> Fn x T A : \<theta>"
  shows "\<exists>\<sigma>. \<theta> = (TArr T \<sigma>) \<and> (\<Gamma>(x \<mapsto> T) \<turnstile> A : \<sigma>)"
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

theorem typing_weaken:
  assumes "\<Gamma> \<turnstile> M : \<tau>" "y \<notin> fvs M"
  shows "\<Gamma>(y \<mapsto> \<sigma>) \<turnstile> M : \<tau>"
using assms proof(induction rule: typing.induct)
  case (tvar \<Gamma> x \<tau>)
    hence "y \<noteq> x" using fvs_simp(1) singletonI by force
    hence "(\<Gamma>(y \<mapsto> \<sigma>)) x = Some \<tau>" using tvar.hyps fun_upd_apply by simp
    thus ?case using typing.tvar by metis
  next
  case (tapp \<Gamma> f \<tau> \<tau>' x)
    from `y \<notin> fvs (App f x)` have "y \<notin> fvs f" "y \<notin> fvs x" using fvs_simp(2) Un_iff by force+
    hence "\<Gamma>(y \<mapsto> \<sigma>) \<turnstile> f : (TArr \<tau> \<tau>')" "\<Gamma>(y \<mapsto> \<sigma>) \<turnstile> x : \<tau>" using tapp.IH by metis+
    thus ?case using typing.tapp by metis
  next
  case (tfn \<Gamma> x \<tau> A \<tau>')
    from `y \<notin> fvs (Fn x \<tau> A)` consider "y = x" | "y \<noteq> x \<and> y \<notin> fvs A"
      using fvs_simp(3) DiffI empty_iff insert_iff by fastforce
    thus ?case proof(cases)
      case 1
        hence "(\<Gamma>(y \<mapsto> \<sigma>)(x \<mapsto> \<tau>)) \<turnstile> A : \<tau>'" using tfn.hyps fun_upd_upd by simp
        thus ?thesis using typing.tfn by metis
      next
      case 2
        hence "y \<noteq> x" "y \<notin> fvs A" by auto
        hence "\<Gamma>(x \<mapsto> \<tau>, y \<mapsto> \<sigma>) \<turnstile> A : \<tau>'" using tfn.IH by metis
        hence "\<Gamma>(y \<mapsto> \<sigma>, x \<mapsto> \<tau>) \<turnstile> A : \<tau>'" using `y \<noteq> x` fun_upd_twist by metis
        thus ?thesis using typing.tfn by metis
      next
    qed
  next
qed


lift_definition infer :: "'a typing_ctx \<Rightarrow> 'a trm \<Rightarrow> type option" is ptrm_infer_type
proof(transfer)
  fix \<Gamma> :: "'a typing_ctx" and X Y :: "'a ptrm"
  assume "X \<approx> Y"
  thus "ptrm_infer_type \<Gamma> X = ptrm_infer_type \<Gamma> Y" using ptrm_infer_type_alpha_equiv by auto
qed

export_code infer in SML

lemma infer_simp:
  shows
    "infer \<Gamma> (Var x) = \<Gamma> x"
    "infer \<Gamma> (App A B) = (case (infer \<Gamma> A, infer \<Gamma> B) of
       (Some (TArr \<tau> \<sigma>), Some \<tau>') \<Rightarrow> (if \<tau> = \<tau>' then Some \<sigma> else None)
     | _ \<Rightarrow> None
     )"
    "infer \<Gamma> (Fn x \<tau> A) = (case infer (\<Gamma>(x \<mapsto> \<tau>)) A of
       Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>)
     | None \<Rightarrow> None
    )"
by((transfer, simp)+)

lemma infer_varE:
  assumes "infer \<Gamma> (Var x) = Some \<tau>"
  shows "\<Gamma> x = Some \<tau>"
using assms by(transfer, simp)

lemma infer_appE:
  assumes "infer \<Gamma> (App A B) = Some \<tau>"
  shows "\<exists>\<sigma>. infer \<Gamma> A = Some (TArr \<sigma> \<tau>) \<and> infer \<Gamma> B = Some \<sigma>"
using assms proof(transfer)
  fix \<Gamma> :: "'a typing_ctx" and A B \<tau>
  assume H: "ptrm_infer_type \<Gamma> (PApp A B) = Some \<tau>"

  have "ptrm_infer_type \<Gamma> A \<noteq> None"
  proof(rule classical)
    assume "\<not>ptrm_infer_type \<Gamma> A \<noteq> None"
    hence "ptrm_infer_type \<Gamma> A = None" by auto
    hence "ptrm_infer_type \<Gamma> (PApp A B) = None" by auto
    hence False using H by auto
    thus ?thesis by blast
  qed
  from this obtain T where *: "ptrm_infer_type \<Gamma> A = Some T" by auto

  have "\<And>x. T \<noteq> TVar x"
  proof(rule classical)
    fix x
    assume "\<not>T \<noteq> TVar x"
    hence "T = TVar x" by auto
    hence "ptrm_infer_type \<Gamma> A = Some (TVar x)" using * by metis
    hence "ptrm_infer_type \<Gamma> (PApp A B) = None" by simp
    hence False using H by auto
    thus "T \<noteq> TVar x" by blast
  qed
  from this obtain \<sigma> \<tau>' where "T = TArr \<sigma> \<tau>'" by(cases T, blast, auto)
  hence *: "ptrm_infer_type \<Gamma> A = Some (TArr \<sigma> \<tau>')" using * by metis

  have "ptrm_infer_type \<Gamma> B \<noteq> None"
  proof(rule classical)
    assume "\<not>ptrm_infer_type \<Gamma> B \<noteq> None"
    hence "ptrm_infer_type \<Gamma> B = None" by auto
    hence "ptrm_infer_type \<Gamma> (PApp A B) = None" using * by auto
    hence False using H by auto
    thus "ptrm_infer_type \<Gamma> B \<noteq> None" by blast
  qed
  from this obtain \<sigma>' where **: "ptrm_infer_type \<Gamma> B = Some \<sigma>'" by auto

  have "\<sigma> = \<sigma>'"
  proof(rule classical)
    assume "\<sigma> \<noteq> \<sigma>'"
    hence "ptrm_infer_type \<Gamma> (PApp A B) = None" using * ** by simp
    hence False using H by auto
    thus "\<sigma> = \<sigma>'" by blast
  qed
  hence **: "ptrm_infer_type \<Gamma> B = Some \<sigma>" using ** by auto

  have "ptrm_infer_type \<Gamma> (PApp A B) = Some \<tau>'" using * ** by auto
  hence "\<tau> = \<tau>'" using H by auto
  hence *: "ptrm_infer_type \<Gamma> A = Some (TArr \<sigma> \<tau>)" using * by auto

  show "\<exists>\<sigma>. ptrm_infer_type \<Gamma> A = Some (TArr \<sigma> \<tau>) \<and> ptrm_infer_type \<Gamma> B = Some \<sigma>"
    using * ** by auto
qed

lemma infer_fnE:
  assumes "infer \<Gamma> (Fn x T A) = Some \<tau>"
  shows "\<exists>\<sigma>. \<tau> = TArr T \<sigma> \<and> infer (\<Gamma>(x \<mapsto> T)) A = Some \<sigma>"
using assms proof(transfer)
  fix x :: 'a and \<Gamma> T A \<tau>
  assume H: "ptrm_infer_type \<Gamma> (PFn x T A) = Some \<tau>"

  have "ptrm_infer_type (\<Gamma>(x \<mapsto> T)) A \<noteq> None"
  proof(rule classical)
    assume "\<not> ptrm_infer_type (\<Gamma>(x \<mapsto> T)) A \<noteq> None"
    hence "ptrm_infer_type (\<Gamma>(x \<mapsto> T)) A = None" by auto
    hence "ptrm_infer_type \<Gamma> (PFn x T A) = None" by auto
    hence False using H by auto
    thus ?thesis by blast
  qed
  from this obtain \<sigma> where *: "ptrm_infer_type (\<Gamma>(x \<mapsto> T)) A = Some \<sigma>" by auto

  have "ptrm_infer_type \<Gamma> (PFn x T A) = Some (TArr T \<sigma>)" using * by auto
  hence "\<tau> = TArr T \<sigma>" using H by auto
  thus "\<exists>\<sigma>. \<tau> = TArr T \<sigma> \<and> ptrm_infer_type (\<Gamma>(x \<mapsto> T)) A = Some \<sigma>"
    using * by auto
qed

lemma infer_sound:
  assumes "infer \<Gamma> M = Some \<tau>"
  shows "\<Gamma> \<turnstile> M : \<tau>"
using assms proof(induction M arbitrary: \<Gamma> \<tau> rule: trm_induct)
  case (1 x)
    hence "\<Gamma> x = Some \<tau>" using infer_varE by metis
    thus ?case using typing.tvar by metis
  next
  case (2 A B)
    from `infer \<Gamma> (App A B) = Some \<tau>` obtain \<sigma>
      where "infer \<Gamma> A = Some (TArr \<sigma> \<tau>)" and "infer \<Gamma> B = Some \<sigma>"
      using infer_appE by metis
    thus ?case using "2.IH" typing.tapp by metis
  next
  case (3 x T A \<Gamma> \<tau>)
    from `infer \<Gamma> (Fn x T A) = Some \<tau>` obtain \<sigma>
      where "\<tau> = TArr T \<sigma>" and "infer (\<Gamma>(x \<mapsto> T)) A = Some \<sigma>"
      using infer_fnE by metis
    thus ?case using "3.IH" typing.tfn by metis
  next
qed

lemma infer_complete:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
  shows "infer \<Gamma> M = Some \<tau>"
using assms proof(induction arbitrary: \<Gamma> \<tau> rule: trm_induct)
  case (1 x)
    hence "\<Gamma> x = Some \<tau>" using typing_varE by metis
    thus ?case by(transfer, simp)
  next
  case (2 A B)
    from this obtain \<sigma> where "\<Gamma> \<turnstile> A : (TArr \<sigma> \<tau>)" "\<Gamma> \<turnstile> B : \<sigma>" using typing_appE by metis
    hence "infer \<Gamma> A = Some (TArr \<sigma> \<tau>)" and "infer \<Gamma> B = Some \<sigma>" using "2.IH" by auto
    thus ?case by(transfer, simp)
  next
  case (3 x T A \<Gamma> S)
    from this obtain \<sigma> where S: "S = TArr T \<sigma>" and "\<Gamma>(x \<mapsto> T) \<turnstile> A : \<sigma>" using typing_fnE by metis
    hence "infer (\<Gamma>(x \<mapsto> T)) A = Some \<sigma>" using "3.IH" by auto
    thus ?case using S by(transfer, simp)
  next
qed

theorem infer_valid:
  shows "(\<Gamma> \<turnstile> M : \<tau>) = (infer \<Gamma> M = Some \<tau>)"
using infer_sound infer_complete by blast


inductive substitutes :: "'a trm \<Rightarrow> 'a \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" where
  var1: "x = y \<Longrightarrow> substitutes (Var x) y M M"
| var2: "x \<noteq> y \<Longrightarrow> substitutes (Var x) y M (Var x)"
| app:  "\<lbrakk>substitutes A x M A'; substitutes B x M B'\<rbrakk> \<Longrightarrow> substitutes (App A B) x M (App A' B')"
| fn:   "\<lbrakk>x \<noteq> y; y \<notin> fvs M; substitutes A x M A'\<rbrakk> \<Longrightarrow> substitutes (Fn y T A) x M (Fn y T A')"

inductive_cases substitutes_varE': "substitutes (Var x) y M X"
lemma substitutes_varE:
  assumes "substitutes (Var x) y M X"
  shows "(x = y \<and> M = X) \<or> (x \<noteq> y \<and> X = Var x)"
by(
  cases rule: substitutes_varE'[where x=x and y=y and M=M and X=X],
  metis assms,
  metis trm_simp(1),
  metis trm_simp(1),
  metis var_not_app,
  metis var_not_fn
)

inductive_cases substitutes_appE': "substitutes (App A B) x M X"
lemma substitutes_appE:
  assumes "substitutes (App A B) x M X"
  shows "\<exists>A' B'. substitutes A x M A' \<and> substitutes B x M B' \<and> X = App A' B'"
by(
  cases rule: substitutes_appE'[where A=A and B=B and x=x and M=M and X=X],
  metis assms,
  metis var_not_app,
  metis var_not_app,
  metis trm_simp(2,3),
  metis app_not_fn
)

inductive_cases substitutes_fnE': "substitutes (Fn y T A) x M X"
lemma substitutes_fnE:
  assumes "substitutes (Fn y T A) x M X"
  shows "x \<noteq> y \<and> y \<notin> fvs M \<and> (\<exists>A'. substitutes A x M A' \<and> X = Fn y T A')"
  apply (cases rule: substitutes_fnE'[where y=y and T=T and A=A and x=x and M=M and X=X])
  apply (metis assms)
  apply (metis var_not_fn)
  apply (metis var_not_fn)
  apply (metis app_not_fn)
proof -
  thm substitutes_fnE'
  case (5 z B A' S)
    thus ?thesis sorry
  next
qed

lemma substitutes_total:
  shows "\<exists>X. substitutes A x M X"
proof(induction "{x} \<union> fvs M" A rule: trm_strong_induct)
  show "finite ({x} \<union> fvs M)" using fvs_finite by auto
  next

  fix y
  show "\<exists>X. substitutes (Var y) x M X"
  proof -
    consider "x = y" | "x \<noteq> y" by auto
    thus ?thesis proof(cases)
      case 1
        obtain X where "X = M" by auto
        hence "substitutes (Var y) x M X" using `x = y` substitutes.var1 by metis
        thus ?thesis by auto
      next
      case 2
        obtain X where "X = (Var y)" by auto
        hence "substitutes (Var y) x M X" using `x \<noteq> y` substitutes.var2 by metis
        thus ?thesis by auto
      next
    qed
  qed
  next

  fix A B
  assume "\<exists>A'. substitutes A x M A'" and "\<exists>B'. substitutes B x M B'"
  from this obtain A' B' where A': "substitutes A x M A'" and B': "substitutes B x M B'" by auto
  show "\<exists>X. substitutes (App A B) x M X"
  proof -
    obtain X where "X = App A' B'" by auto
    hence "substitutes (App A B) x M X" using A' B' substitutes.app by metis
    thus ?thesis by auto
  qed
  next

  fix y T A
  assume "y \<notin> ({x} \<union> fvs M)" and "\<exists>A'. substitutes A x M A'"
  from this obtain A' where A': "substitutes A x M A'" by auto
  from `y \<notin> ({x} \<union> fvs M)` have "y \<noteq> x" "y \<notin> fvs M" by auto
  show "\<exists>X. substitutes (Fn y T A) x M X"
  proof -
    obtain X where "X = Fn y T A'" by auto
    hence "substitutes (Fn y T A) x M X" using substitutes.fn `y \<noteq> x` `y \<notin> fvs M` A' by metis
    thus ?thesis by auto
  qed
  next
qed

lemma substitutes_unique:
  assumes "substitutes A x M B" "substitutes A x M C"
  shows "B = C"
using assms proof(induction A arbitrary: B C rule: trm_induct)
  case (1 y)
    thus ?case using substitutes_varE by metis
  next
  case (2 X Y)
    thus ?case using substitutes_appE by metis
  next
  case (3 y T A)
    thus ?case using substitutes_fnE by metis
  next
qed

lemma substitutes_function:
  shows "\<exists>! X. substitutes A x M X"
using substitutes_total substitutes_unique by metis

definition subst :: "'a trm \<Rightarrow> 'a \<Rightarrow> 'a trm \<Rightarrow> 'a trm" ("_[_ ::= _]") where
  "subst A x M \<equiv> (THE X. substitutes A x M X)"

lemma subst_simp_var1:
  shows "(Var x)[x ::= M] = M"
unfolding subst_def by(rule, metis substitutes.var1, metis substitutes_function substitutes.var1)

lemma subst_simp_var2:
  assumes "x \<noteq> y"
  shows "(Var x)[y ::= M] = Var x"
unfolding subst_def by(
  rule,
  metis substitutes.var2 assms,
  metis substitutes_function substitutes.var2 assms
)

lemma subst_simp_app:
  shows "(App A B)[x ::= M] = App (A[x ::= M]) (B[x ::= M])"
unfolding subst_def proof
  obtain A' B' where A': "A' = (A[x ::= M])" and B': "B' = (B[x ::= M])" by auto
  hence "substitutes A x M A'" "substitutes B x M B'"
    unfolding subst_def
    using substitutes_function theI by metis+
  hence "substitutes (App A B) x M (App A' B')" using substitutes.app by metis
  thus *: "substitutes (App A B) x M (App (THE X. substitutes A x M X) (THE X. substitutes B x M X))"
    using A' B' unfolding subst_def by metis

  fix X
  assume "substitutes (App A B) x M X"
  thus "X = App (THE X. substitutes A x M X) (THE X. substitutes B x M X)"
    using substitutes_function * by metis
qed

lemma subst_simp_fn:
  assumes "x \<noteq> y" "y \<notin> fvs M"
  shows "(Fn y T A)[x ::= M] = Fn y T (A[x ::= M])"
unfolding subst_def proof
  obtain A' where A': "A' = (A[x ::= M])" by auto
  hence "substitutes A x M A'" unfolding subst_def using substitutes_function theI by metis
  hence "substitutes (Fn y T A) x M (Fn y T A')" using substitutes.fn assms by metis
  thus *: "substitutes (Fn y T A) x M (Fn y T (THE X. substitutes A x M X))"
    using A' unfolding subst_def by metis

  fix X
  assume "substitutes (Fn y T A) x M X"
  thus "X = Fn y T (THE X. substitutes A x M X)" using substitutes_function * by metis
qed

lemma subst_fvs:
  shows "fvs (M[z ::= N]) \<subseteq> (fvs M - {z}) \<union> fvs N"
proof(induction M rule: trm_strong_induct[where S="{z} \<union> fvs N"])
  show "finite ({z} \<union> fvs N)" using fvs_finite by auto
  next

  case (1 x)
    thus ?case
      using subst_simp_var1 subst_simp_var2
      by(cases "x = z", auto simp add: fvs_simp)
  next
  case (2 A B)
    hence "fvs (A[z ::= N]) \<union> fvs (B[z ::= N]) \<subseteq> fvs A \<union> fvs B - {z} \<union> fvs N"
      by auto
    hence "fvs (App (A[z ::= N]) (B[z ::= N])) \<subseteq> fvs (App A B) - {z} \<union> fvs N"
      using fvs_simp(2) by metis
    thus ?case using subst_simp_app by metis
  next
  case (3 x T A)
    hence "x \<noteq> z" "x \<notin> fvs N" by auto
    from "3.IH" have "(fvs (A[z ::= N]) - {x}) \<subseteq> (fvs A - {x}) - {z} \<union> fvs N" by auto
    hence "fvs (Fn x T (A[z ::= N])) \<subseteq> fvs (Fn x T A) - {z} \<union> fvs N" using fvs_simp(3) by metis
    thus ?case using subst_simp_fn `x \<noteq> z` `x \<notin> fvs N` by metis
  next
qed

lemma subst_prm:
  shows "(\<pi> \<cdot> (M[z ::= N])) = ((\<pi> \<cdot> M)[\<pi> $ z ::= \<pi> \<cdot> N])"
proof(induction M rule: trm_strong_induct[where S="{z} \<union> fvs N"])
  show "finite ({z} \<union> fvs N)" using fvs_finite by auto
  next

  case (1 x)
    consider "x = z" | "x \<noteq> z" by auto
    thus ?case proof(cases)
      case 1
        hence
          "(\<pi> \<cdot> ((Var x)[z ::= N])) = \<pi> \<cdot> N"
          "((\<pi> \<cdot> (Var x))[\<pi> $ z ::= \<pi> \<cdot> N]) = \<pi> \<cdot> N"
          using subst_simp_var1 by (metis, metis trm_prm_simp(1))
        thus ?thesis by auto
      next
      case 2
        hence "\<pi> $ x \<noteq> \<pi> $ z" using prm_apply_unequal by metis
        hence
          "(\<pi> \<cdot> ((Var x)[z ::= N])) = Var (\<pi> $ x)"
          "((\<pi> \<cdot> (Var x))[\<pi> $ z ::= \<pi> \<cdot> N]) = Var (\<pi> $ x)"
          using subst_simp_var2 trm_prm_simp(1) `x \<noteq> z` by metis+
        thus ?thesis by auto
      next
    qed
  next
  case (2 A B)
    thus ?case using subst_simp_app trm_prm_simp(2) by metis
  next
  case (3 x T A)
    hence "x \<noteq> z" "x \<notin> fvs N" by auto

    have 1: "(\<pi> \<cdot> ((Fn x T A)[z ::= N])) = Fn (\<pi> $ x) T ((\<pi> \<cdot> A)[\<pi> $ z ::= \<pi> \<cdot> N])"
    proof -
      have "(\<pi> \<cdot> ((Fn x T A)[z ::= N])) = \<pi> \<cdot> (Fn x T (A[z ::= N]))"
        using subst_simp_fn `x \<noteq> z` `x \<notin> fvs N` by metis
      also have "... = Fn (\<pi> $ x) T (\<pi> \<cdot> (A[z ::= N]))"
        using trm_prm_simp(3) by metis
      also have "... = Fn (\<pi> $ x) T ((\<pi> \<cdot> A)[\<pi> $ z ::= \<pi> \<cdot> N])"
        using "3.IH" by metis
      finally show ?thesis.
    qed

    have 2: "(\<pi> \<cdot> (Fn x T A))[\<pi> $ z ::= \<pi> \<cdot> N] = Fn (\<pi> $ x) T ((\<pi> \<cdot> A)[\<pi> $ z ::= \<pi> \<cdot> N])"
    proof -
      have "\<pi> $ x \<noteq> \<pi> $ z" using prm_apply_unequal `x \<noteq> z` by metis
      have "\<pi> $ x \<notin> fvs (\<pi> \<cdot> N)" using `x \<notin> fvs N` using trm_prm_fvs prm_set_notmembership by metis

      have "((\<pi> \<cdot> (Fn x T A))[\<pi> $ z ::= \<pi> \<cdot> N]) = ((Fn (\<pi> $ x) T (\<pi> \<cdot> A))[\<pi> $ z ::= \<pi> \<cdot> N])"
        using trm_prm_simp(3) by metis
      also have "... = Fn (\<pi> $ x) T ((\<pi> \<cdot> A)[\<pi> $ z ::= \<pi> \<cdot> N])"
        using subst_simp_fn `\<pi> $ x \<noteq> \<pi> $ z` `\<pi> $ x \<notin> fvs (\<pi> \<cdot> N)` by metis
      finally show ?thesis.
    qed
    from 1 and 2 show ?case by auto
  next
qed

lemma typing_subst:
  assumes "\<Gamma>(z \<mapsto> \<tau>) \<turnstile> M : \<sigma>" "\<Gamma> \<turnstile> N : \<tau>"
  shows "\<Gamma> \<turnstile> M[z ::= N] : \<sigma>"
using assms proof(induction M arbitrary: \<Gamma> \<sigma> rule: trm_strong_depth_induct[where S="{z} \<union> fvs N"])
  show "finite ({z} \<union> fvs N)" using fvs_finite by auto
  next

  case (1 x)
    hence *: "(\<Gamma>(z \<mapsto> \<tau>)) x = Some \<sigma>" using typing_varE by metis

    consider "x = z" | "x \<noteq> z" by auto
    thus ?case proof(cases)
      case 1
        hence "(\<Gamma>(x \<mapsto> \<tau>)) x = Some \<sigma>" using * by metis
        hence "\<tau> = \<sigma>" by auto
        thus ?thesis using `\<Gamma> \<turnstile> N : \<tau>` subst_simp_var1 `x = z` by metis
      next
      case 2
        hence "\<Gamma> x = Some \<sigma>" using * by auto
        hence "\<Gamma> \<turnstile> Var x : \<sigma>" using typing.tvar by metis
        thus ?thesis using `x \<noteq> z` subst_simp_var2 by metis
      next
    qed
  next
  case (2 A B)
    have *: "depth A < depth (App A B) \<and> depth B < depth (App A B)"
      using depth_app by auto

    from `\<Gamma>(z \<mapsto> \<tau>) \<turnstile> App A B : \<sigma>` obtain \<sigma>' where
      "\<Gamma>(z \<mapsto> \<tau>) \<turnstile> A : (TArr \<sigma>' \<sigma>)"
      "\<Gamma>(z \<mapsto> \<tau>) \<turnstile> B : \<sigma>'"
      using typing_appE by metis
    hence
      "\<Gamma> \<turnstile> (A[z ::= N]) : (TArr \<sigma>' \<sigma>)"
      "\<Gamma> \<turnstile> (B[z ::= N]) : \<sigma>'"
      using 2 * by metis+
    hence "\<Gamma> \<turnstile> App (A[z ::= N]) (B[z ::= N]) : \<sigma>" using typing.tapp by metis
    thus ?case using subst_simp_app by metis
  next
  case (3 x T A)
    hence "x \<noteq> z" "x \<notin> fvs N" by auto
    hence *: "\<Gamma>(x \<mapsto> T) \<turnstile> N : \<tau>" using typing_weaken 3 by metis
    have **: "depth A < depth (Fn x T A)" using depth_fn.

    from `\<Gamma>(z \<mapsto> \<tau>) \<turnstile> Fn x T A : \<sigma>` obtain \<sigma>' where
      "\<sigma> = TArr T \<sigma>'"
      "\<Gamma>(z \<mapsto> \<tau>)(x \<mapsto> T) \<turnstile> A : \<sigma>'"
      using typing_fnE by metis
    hence "\<Gamma>(x \<mapsto> T)(z \<mapsto> \<tau>) \<turnstile> A : \<sigma>'" using `x \<noteq> z` fun_upd_twist by metis
    hence "\<Gamma>(x \<mapsto> T) \<turnstile> A[z ::= N] : \<sigma>'" using 3 * ** by metis
    hence "\<Gamma> \<turnstile> Fn x T (A[z ::= N]) : \<sigma>" using typing.tfn `\<sigma> = TArr T \<sigma>'` by metis
    thus ?case using `x \<noteq> z` `x \<notin> fvs N` subst_simp_fn by metis
  next
qed


inductive beta_reduction :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" ("_ \<rightarrow>\<beta> _") where
  beta: "(App (Fn x T A) M) \<rightarrow>\<beta> (A[x ::= M])"
| app1: "A \<rightarrow>\<beta> A' \<Longrightarrow> (App A B) \<rightarrow>\<beta> (App A' B)"
| app2: "B \<rightarrow>\<beta> B' \<Longrightarrow> (App A B) \<rightarrow>\<beta> (App A B')"
| fn:   "A \<rightarrow>\<beta> A' \<Longrightarrow> (Fn x T A) \<rightarrow>\<beta> (Fn x T A')"

lemma beta_reduction_fvs:
  assumes "M \<rightarrow>\<beta> M'"
  shows "fvs M' \<subseteq> fvs M"
using assms proof(induction)
  case (beta x T A M)
    thus ?case using fvs_simp(2) fvs_simp(3) subst_fvs by metis
  next
  case (app1 A A' B)
    hence "fvs A' \<union> fvs B \<subseteq> fvs A \<union> fvs B" by auto
    thus ?case using fvs_simp(2) by metis
  next
  case (app2 B B' A)
    hence "fvs A \<union> fvs B' \<subseteq> fvs A \<union> fvs B" by auto
    thus ?case using fvs_simp(2) by metis
  next
  case (fn A A' x T)
    hence "fvs A' - {x} \<subseteq> fvs A - {x}" by auto
    thus ?case using fvs_simp(3) by metis
  next
qed

lemma beta_reduction_prm:
  assumes "M \<rightarrow>\<beta> M'"
  shows "(\<pi> \<cdot> M) \<rightarrow>\<beta> (\<pi> \<cdot> M')"
using assms proof(induction)
  case (beta x T A M)
    thus ?case using beta_reduction.beta trm_prm_simp(2) trm_prm_simp(3) subst_prm by metis
  next
  case (app1 A A' B)
    thus ?case using beta_reduction.app1 trm_prm_simp(2) by metis
  next
  case (app2 B B' A)
    thus ?case using beta_reduction.app2 trm_prm_simp(2) by metis
  next
  case (fn A A' x T)
    thus ?case using beta_reduction.fn trm_prm_simp(3) by metis
  next
qed

lemma beta_reduction_left_varE:
  assumes "(Var x) \<rightarrow>\<beta> M'"
  shows "False"
using assms by(cases, auto simp add: var_not_app var_not_fn)

lemma beta_reduction_left_appE:
  assumes "(App A B) \<rightarrow>\<beta> M'"
  shows "
    (\<exists>x T X. A = (Fn x T X) \<and> M' = (X[x ::= B])) \<or>
    (\<exists>A'. (A \<rightarrow>\<beta> A') \<and> M' = App A' B) \<or>
    (\<exists>B'. (B \<rightarrow>\<beta> B') \<and> M' = App A B')
  "
using assms by(
  cases,
  metis trm_simp(2, 3),
  metis trm_simp(2, 3),
  metis trm_simp(2, 3),
  metis app_not_fn
)

lemma beta_reduction_left_fnE:
  assumes "(Fn x T A) \<rightarrow>\<beta> M'"
  shows "\<exists>A'. (A \<rightarrow>\<beta> A') \<and> M' = (Fn x T A')"
using assms proof(cases, metis app_not_fn, metis app_not_fn, metis app_not_fn)
  case (fn B B' y S)
    consider "x = y \<and> T = S \<and> A = B" | "x \<noteq> y \<and> T = S \<and> x \<notin> fvs B \<and> A = [x \<leftrightarrow> y] \<cdot> B"
      using trm_simp(4) `Fn x T A = Fn y S B` by metis
    thus ?thesis proof(cases)
      case 1
        thus ?thesis using fn by auto
      next
      case 2
        thus ?thesis using fn beta_reduction_fvs beta_reduction_prm fn_eq by fastforce
      next
    qed
  next
qed

lemma preservation':
  assumes "\<Gamma> \<turnstile> M : \<tau>" and "M \<rightarrow>\<beta> M'"
  shows "\<Gamma> \<turnstile> M' : \<tau>"
using assms proof(induction arbitrary: M' rule: typing.induct)
  case (tvar \<Gamma> x \<tau>)
    thus ?case using beta_reduction_left_varE by metis
  next
  case (tapp \<Gamma> A \<tau> \<sigma> B M')
    from `(App A B) \<rightarrow>\<beta> M'` consider
      "(\<exists>x T X. A = (Fn x T X) \<and> M' = (X[x ::= B]))" |
      "(\<exists>A'. (A \<rightarrow>\<beta> A') \<and> M' = App A' B)" |
      "(\<exists>B'. (B \<rightarrow>\<beta> B') \<and> M' = App A B')" using beta_reduction_left_appE by metis

    thus ?case proof(cases)
      case 1
        from this obtain x T X where "A = Fn x T X" and *: "M' = (X[x ::= B])" by auto

        have "\<Gamma>(x \<mapsto> \<tau>) \<turnstile> X : \<sigma>" using typing_fnE `\<Gamma> \<turnstile> A : (TArr \<tau> \<sigma>)` `A = Fn x T X` type.inject
          by blast
        hence "\<Gamma> \<turnstile> (X[x ::= B]) : \<sigma>" using typing_subst `\<Gamma> \<turnstile> B : \<tau>` by metis
        thus ?thesis using * by auto
      next
      case 2
        from this obtain A' where "A \<rightarrow>\<beta> A'" and *: "M' = (App A' B)" by auto
        hence "\<Gamma> \<turnstile> A' : (TArr \<tau> \<sigma>)" using tapp.IH(1) by metis
        hence "\<Gamma> \<turnstile> (App A' B) : \<sigma>" using `\<Gamma> \<turnstile> B : \<tau>` typing.tapp by metis
        thus ?thesis using * by auto
      next
      case 3
        from this obtain B' where "B \<rightarrow>\<beta> B'" and *: "M' = (App A B')" by auto
        hence "\<Gamma> \<turnstile> B' : \<tau>" using tapp.IH(2) by metis
        hence "\<Gamma> \<turnstile> (App A B') : \<sigma>" using `\<Gamma> \<turnstile> A : (TArr \<tau> \<sigma>)` typing.tapp by metis
        thus ?thesis using * by auto
      next
    qed
  next
  case (tfn \<Gamma> x T A \<sigma>)
    from this obtain A' where "A \<rightarrow>\<beta> A'" and *: "M' = (Fn x T A')"
      using beta_reduction_left_fnE by metis
    hence "\<Gamma>(x \<mapsto> T) \<turnstile> A' : \<sigma>" using tfn.IH by metis
    hence "\<Gamma> \<turnstile> (Fn x T A') : (TArr T \<sigma>)" using typing.tfn by metis
    thus ?case using * by auto
  next
qed

inductive NF :: "'a trm \<Rightarrow> bool" where
  var: "NF (Var x)"
| app_var: "NF B \<Longrightarrow> NF (App (Var x) B)"
| app_app: "\<lbrakk>NF (App C D); NF B\<rbrakk> \<Longrightarrow> NF (App (App C D) B)"
| fn: "NF A \<Longrightarrow> NF (Fn x T A)"

theorem progress:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
  shows "NF M \<or> (\<exists>M'. (M \<rightarrow>\<beta> M'))"
using assms proof(induction M arbitrary: \<Gamma> \<tau> rule: trm_induct)
  case (1 x)
    thus ?case using NF.var by metis
  next
  case (2 A B)
    from `\<Gamma> \<turnstile> App A B : \<tau>` obtain \<sigma>
      where "\<Gamma> \<turnstile> A : (TArr \<sigma> \<tau>)" and "\<Gamma> \<turnstile> B : \<sigma>"
      using typing_appE by metis
    hence A: "NF A \<or> (\<exists>A'. (A \<rightarrow>\<beta> A'))" and B: "NF B \<or> (\<exists>B'. (B \<rightarrow>\<beta> B'))"
      using "2.IH" by auto

    consider "NF B" | "\<exists>B'. (B \<rightarrow>\<beta> B')" using B by auto
    thus ?case proof(cases)
      case 1
        consider "NF A" | "\<exists>A'. (A \<rightarrow>\<beta> A')" using A by auto
        thus ?thesis proof(cases)
          case 1
            thus ?thesis proof(induction A rule: trm_cases)
              case (1 x)
                thus ?thesis using `NF B` NF.app_var by metis
              next
              case (2 C D)
                thus ?thesis using `NF B` NF.app_app by metis
              next
              case (3 y S X)
                hence "(App A B) \<rightarrow>\<beta> (X[y ::= B])" using beta_reduction.beta by metis
                thus ?thesis by auto
              next
            qed
          next
          case 2
            thus ?thesis using beta_reduction.app1 by metis
          next
        qed
      next
      case 2
        thus ?thesis using beta_reduction.app2 by metis
      next
    qed
  next
  case (3 x T A)
    from `\<Gamma> \<turnstile> Fn x T A : \<tau>` obtain \<sigma>
      where "\<tau> = TArr T \<sigma>" and "\<Gamma>(x \<mapsto> T) \<turnstile> A : \<sigma>"
      using typing_fnE by metis
    from `\<Gamma>(x \<mapsto> T) \<turnstile> A : \<sigma>` consider "NF A" | "\<exists>A'. (A \<rightarrow>\<beta> A')"
      using "3.IH" by metis

    thus ?case proof(cases)
      case 1
        thus ?thesis using NF.fn by metis
      next
      case 2
        from this obtain A' where "A \<rightarrow>\<beta> A'" by auto
        obtain M' where "M' = Fn x T A'" by auto
        hence "(Fn x T A) \<rightarrow>\<beta> M'" using `A \<rightarrow>\<beta> A'` beta_reduction.fn by metis
        thus ?thesis by auto
      next
    qed
  next
qed

inductive beta_reduces :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" ("_ \<rightarrow>\<beta>\<^sup>* _") where
  reflexive:  "M \<rightarrow>\<beta>\<^sup>* M"
| transitive: "\<lbrakk>M \<rightarrow>\<beta>\<^sup>* M'; M' \<rightarrow>\<beta> M''\<rbrakk> \<Longrightarrow> M \<rightarrow>\<beta>\<^sup>* M''"

lemma beta_reduces_composition:
  assumes "A' \<rightarrow>\<beta>\<^sup>* A''" and "A \<rightarrow>\<beta>\<^sup>* A'"
  shows "A \<rightarrow>\<beta>\<^sup>* A''"
using assms proof(induction)
  case (reflexive B)
    thus ?case.
  next
  case (transitive B B' B'')
    thus ?case using beta_reduces.transitive by metis
  next
qed

lemma beta_reduces_fvs:
  assumes "A \<rightarrow>\<beta>\<^sup>* A'"
  shows "fvs A' \<subseteq> fvs A"
using assms proof(induction)
  case (reflexive M)
    thus ?case by auto
  next
  case (transitive M M' M'')
    hence "fvs M'' \<subseteq> fvs M'" using beta_reduction_fvs by metis
    thus ?case using `fvs M' \<subseteq> fvs M` by auto
  next
qed

lemma beta_reduces_app_left:
  assumes "A \<rightarrow>\<beta>\<^sup>* A'"
  shows "(App A B) \<rightarrow>\<beta>\<^sup>* (App A' B)"
using assms proof(induction)
  case (reflexive A)
    thus ?case using beta_reduces.reflexive.
  next
  case (transitive A A' A'')
    thus ?case using beta_reduces.transitive beta_reduction.app1 by metis
  next
qed

lemma beta_reduces_app_right:
  assumes "B \<rightarrow>\<beta>\<^sup>* B'"
  shows "(App A B) \<rightarrow>\<beta>\<^sup>* (App A B')"
using assms proof(induction)
  case (reflexive B)
    thus ?case using beta_reduces.reflexive.
  next
  case (transitive B B' B'')
    thus ?case using beta_reduces.transitive beta_reduction.app2 by metis
  next
qed

theorem preservation:
  assumes "M \<rightarrow>\<beta>\<^sup>* M'" "\<Gamma> \<turnstile> M : \<tau>"
  shows "\<Gamma> \<turnstile> M' : \<tau>"
using assms proof(induction)
  case (reflexive M)
    thus ?case.
  next
  case (transitive M M' M'')
    thus ?case using preservation' by metis
  next
qed

theorem safety:
  assumes "M \<rightarrow>\<beta>\<^sup>* M'" "\<Gamma> \<turnstile> M : \<tau>"
  shows "NF M' \<or> (\<exists>M''. (M' \<rightarrow>\<beta> M''))"
using assms proof(induction)
  case (reflexive M)
    thus ?case using progress by metis
  next
  case (transitive M M' M'')
    hence "\<Gamma> \<turnstile> M' : \<tau>" using preservation by metis
    hence "\<Gamma> \<turnstile> M'' : \<tau>" using preservation' `M' \<rightarrow>\<beta> M''` by metis
    thus ?case using progress by metis
  next
qed

end
end