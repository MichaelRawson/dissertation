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

lemma trm_distinct:
  shows
    "Var x \<noteq> App A B"
    "App A B \<noteq> Var x"
    "Var x \<noteq> Fn y T Y"
    "Fn y T Y \<noteq> Var x"
    "App A B \<noteq> Fn y T Y"
    "Fn y T Y \<noteq> App A B"
  apply (metis var_not_app)
  apply (metis var_not_app)
  apply (metis var_not_fn)
  apply (metis var_not_fn)
  apply (metis app_not_fn)
  apply (metis app_not_fn)
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



context fresh begin

lemma trm_strong_induct:
  fixes P :: "'a set \<Rightarrow> 'a trm \<Rightarrow> bool"
  assumes
    "\<And>S x. finite S \<Longrightarrow> P S (Var x)"
    "\<And>S A B. \<lbrakk>finite S; \<And>S. finite S \<Longrightarrow> P S A; \<And>S. finite S \<Longrightarrow> P S B\<rbrakk> \<Longrightarrow> P S (App A B)"
    "\<And>S x T A. \<lbrakk>finite S; x \<notin> S; \<And>S. finite S \<Longrightarrow> P S A\<rbrakk> \<Longrightarrow> P S (Fn x T A)"
    "finite S"
  shows "P S M"
using `finite S` proof(induction "depth M" arbitrary: M S rule: less_induct)
  fix M :: "'a trm" and S :: "'a set"
  assume "\<And>K S. \<lbrakk>depth K < depth M; finite S\<rbrakk> \<Longrightarrow> P S K" and "finite S"
  thus "P S M"
  proof(induction M rule: trm_induct)
    case (1 x)
      thus ?case using assms(1) by metis
    next
    case (2 A B)
      have "depth A < depth (App A B)" and "depth B < depth (App A B)" 
        by ((transfer, auto)+)

      have "\<And>S. finite S \<Longrightarrow> P S A" and "\<And>S. finite S \<Longrightarrow> P S B"
        using "2.prems" `depth A < depth (App A B)` `depth B < depth (App A B)`
        by auto

      thus ?case using assms(2) `finite S` by auto
    next
    case (3 x T A)
      hence "finite ({x} \<union> fvs A \<union> S)" 
        using fvs_finite finite.emptyI finite.insertI finite_UnI by blast
      obtain y where "y = fresh_in ({x} \<union> fvs A \<union> S)" by auto
      hence "y \<notin> ({x} \<union> fvs A \<union> S)" using fresh_axioms unfolding class.fresh_def
        using `finite ({x} \<union> fvs A \<union> S)` by metis
      hence "y \<noteq> x" "y \<notin> fvs A" "y \<notin> S" by auto

      have "\<And>S. finite S \<Longrightarrow> P S ([x \<leftrightarrow> y] \<cdot> A)"
      using "3.prems"(1) proof -
        fix S :: "'a set"
        assume "finite S"
        assume *: "\<And>K S. \<lbrakk>depth K < depth (Fn x T A); finite S\<rbrakk> \<Longrightarrow> P S K"

        have "depth A = depth ([x \<leftrightarrow> y] \<cdot> A)" using depth_prm.
        moreover have "depth A < depth (Fn x T A)" by (transfer, auto)
        ultimately have "depth ([x \<leftrightarrow> y] \<cdot> A) < depth (Fn x T A)" by metis

        thus "P S ([x \<leftrightarrow> y] \<cdot> A)" using * `finite S` by metis
      qed

      have "P S (Fn y T ([x \<leftrightarrow> y] \<cdot> A))"
        using assms(3) `finite S` `y \<notin> S` `\<And>S. finite S \<Longrightarrow> P S ([x \<leftrightarrow> y] \<cdot> A)` 
        by metis
     
      have "Fn y T ([x \<leftrightarrow> y] \<cdot> A) = Fn x T A"
      using `y \<noteq> x` `y \<notin> fvs A` proof(transfer')
        fix x y :: 'a and X T
        assume "y \<noteq> x" "y \<notin> ptrm_fvs X"
  
        have "[x \<leftrightarrow> y] \<bullet> X \<approx> [y \<leftrightarrow> x] \<bullet> X"
          using ptrm_alpha_equiv_reflexive prm_unit_commutes by metis
        thus "PFn y T ([x \<leftrightarrow> y] \<bullet> X) \<approx> PFn x T X"
          using `y \<noteq> x` `y \<notin> ptrm_fvs X` ptrm_alpha_equiv.fn2 by metis
      qed

      thus ?case
        using `P S (Fn y T ([x \<leftrightarrow> y] \<cdot> A))` `Fn y T ([x \<leftrightarrow> y] \<cdot> A) = Fn x T A`
        by auto
    next
  qed
qed

lemma trm_prm_id:
  shows "\<epsilon> \<cdot> M = M"
by(induction M rule: trm_induct, auto simp add: trm_prm_simp prm_apply_id)

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
  assumes "y \<notin> fvs M"
  shows "(\<Gamma> \<turnstile> M : \<tau>) = (\<Gamma>(y \<mapsto> \<sigma>) \<turnstile> M : \<tau>)"
using assms proof(induction "fvs M" M arbitrary: \<Gamma> \<tau> rule: trm_strong_induct)
  show "finite (fvs M)" using fvs_finite.

  case (1 x \<Gamma> \<tau>)
    have "fvs (Var x) = {x}" using fvs_simp(1).
    hence "y \<notin> {x}" using `y \<notin> fvs (Var x)` by auto
    hence "y \<noteq> x" by auto
    hence "\<Gamma> x = (\<Gamma>(y \<mapsto> \<sigma>)) x" by simp
    thus ?case using typing_varE typing.tvar by metis 
  next
  case (2 A B \<Gamma> \<tau>)
    have "finite (fvs A)" and "finite (fvs B)" using fvs_finite by auto
    have "fvs (App A B) = fvs A \<union> fvs B" using fvs_simp(2).
    hence "y \<notin> fvs A \<union> fvs B" using `y \<notin> fvs (App A B)` by auto
    hence "y \<notin> fvs A" and "y \<notin> fvs B" by auto
    thus ?case
      using "2.hyps" `finite (fvs A)` `finite (fvs B)` typing.tapp typing_appE typing.simps
      by metis
  next
  case (3 x T A \<Gamma> \<tau>)
    have "finite (fvs A)" using fvs_finite by auto
    have "fvs (Fn x T A) = fvs A - {x}" using fvs_simp(3).
    hence "y \<notin> fvs A - {x}" using `y \<notin> fvs (Fn x T A)` by auto
    from this consider "y \<notin> fvs A" | "y = x" by auto
    thus ?case proof(cases)
      case 1
        thus ?thesis 
          using "3.hyps"(3) `finite (fvs A)` fun_upd_twist fun_upd_upd tfn typing_fnE
          by smt
      next
      case 2
        hence "\<Gamma>(x \<mapsto> T) = \<Gamma>(y \<mapsto> \<sigma>)(x \<mapsto> T)" by simp
        thus ?thesis using typing.tfn typing_fnE by metis
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

theorem infer_valid:
  shows "(\<Gamma> \<turnstile> M : \<tau>) = (infer \<Gamma> M = Some \<tau>)"
proof -
  have 1: "\<Gamma> \<turnstile> M : \<tau> \<Longrightarrow> infer \<Gamma> M = Some \<tau>"
  proof(induction arbitrary: \<Gamma> \<tau> rule: trm_induct)
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

  have 2: "infer \<Gamma> M = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> M : \<tau>"
  proof(induction M arbitrary: \<Gamma> \<tau> rule: trm_induct)
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

  show ?thesis using 1 and 2 by blast
qed



lift_definition subst :: "'a trm \<Rightarrow> 'a \<Rightarrow> 'a trm \<Rightarrow> 'a trm" ("_[_ ::= _]") is ptrm_subst
  using ptrm_subst_alpha_equiv_left ptrm_subst_alpha_equiv_right ptrm_alpha_equiv_transitive
  by blast

lemma subst_simp:
  shows
    "(Var x)[z ::= M] = (if x = z then M else Var x)"
    "(App A B)[z ::= M] = App (A[z ::= M]) (B[z ::= M])"
    "(Fn x T A)[z ::= M] =
       (if x = z
         then Fn x T A
         else (let y = fresh_in ({z} \<union> fvs A \<union> fvs M) in Fn y T (([x \<leftrightarrow> y] \<cdot> A)[z ::= M])))"
  apply (transfer, simp add: ptrm_alpha_equiv_reflexive)[]
  apply (transfer, simp add: ptrm_alpha_equiv_reflexive)[]
  apply (transfer', simp add: ptrm_alpha_equiv_reflexive)[]
done

lemma subst_fvs:
  shows "fvs (M[z ::= N]) \<subseteq> (fvs M - {z}) \<union> fvs N"
proof(induction "depth M" arbitrary: M rule: less_induct)
  fix M :: "'a trm"
  assume IH: "\<And>K. depth K < depth M \<Longrightarrow> fvs (K[z ::= N]) \<subseteq> fvs K - {z} \<union> fvs N"
  thus "fvs (M[z ::= N]) \<subseteq> fvs M - {z} \<union> fvs N"
  proof(induction M rule: trm_cases)
    case (1 x)
      hence M: "M = Var x" by auto
      consider "x = z" | "x \<noteq> z" by auto
      thus ?case proof(cases)
        case 1
          thus ?thesis using M subst_simp Un_upper2 by simp
        next
        case 2
          thus ?thesis
            using
              M subst_simp(1) fvs_simp(1) Diff_empty Diff_insert0 insert_Diff le_supI1 order_refl
              singleton_insert_inj_eq
            by metis
        next
      qed
    next
    case (2 A B)
      hence M: "M = App A B" by auto
      have "depth A < depth (App A B)" and "depth B < depth (App A B)"
        by((transfer, auto)+)
      hence "depth A < depth M" and "depth B < depth M" using M by auto
      hence
        A:"fvs (A[z ::= N]) \<subseteq> fvs A - {z} \<union> fvs N" and
        B: "fvs (B[z ::= N]) \<subseteq> fvs B - {z} \<union> fvs N"
        using IH by auto

      have "fvs ((App A B)[z ::= N]) = fvs (App (A[z ::= N]) (B[z ::= N]))"
        using subst_simp(2) by auto
      also have "... = fvs (A[z ::= N]) \<union> fvs (B[z ::= N])"
        using fvs_simp(2) by metis
      also have "... \<subseteq> (fvs A - {z} \<union> fvs N) \<union> (fvs B - {z} \<union> fvs N)"
        using A B by auto
      also have "... = (fvs A \<union> fvs B) - {z} \<union> fvs N" by auto
      also have "... = fvs (App A B) - {z} \<union> fvs N" using fvs_simp(2) by metis
      finally show ?case using M by metis
    next
    case (3 x T A)
      hence M: "M = Fn x T A" by auto
      consider "z = x" | "z \<noteq> x" by auto
      thus ?case proof(cases)
        case 1
          hence "fvs ((Fn x T A)[z ::= N]) = fvs (Fn x T A)"
            using subst_simp(3) by simp
          also have "... = fvs A - {x}" using fvs_simp(3) by metis
          also have "... = fvs A - {x} - {z}" using `z = x` by auto
          also have "... \<subseteq> fvs A - {x} - {z} \<union> fvs N" by auto
          also have "... = fvs (Fn x T A) - {z} \<union> fvs N" using fvs_simp(3) by metis
          finally show ?thesis using M by metis
        next
        case 2
          obtain y where y: "y = fresh_in ({z} \<union> fvs A \<union> fvs N)" by auto
          have "depth ([x \<leftrightarrow> y] \<cdot> A) = depth A" using depth_prm by metis
          hence "depth ([x \<leftrightarrow> y] \<cdot> A) < depth (Fn x T A)" by(transfer', auto)
          hence "depth ([x \<leftrightarrow> y] \<cdot> A) < depth M" using M by auto
          hence A: "fvs (([x \<leftrightarrow> y] \<cdot> A)[z ::= N]) \<subseteq> fvs ([x \<leftrightarrow> y] \<cdot> A) - {z} \<union> fvs N"
            using IH by metis

          have "finite ({z} \<union> fvs A \<union> fvs N)" using fvs_finite by auto
          hence "y \<notin> ({z} \<union> fvs A \<union> fvs N)"
            using y fresh_axioms unfolding class.fresh_def by metis
          hence "y \<noteq> z" and "y \<notin> fvs A" and "y \<notin> fvs N" by auto

          have "fvs ((Fn x T A)[z ::= N]) = fvs (Fn y T (([x \<leftrightarrow> y] \<cdot> A)[z ::= N]))"
            using subst_simp(3) `z \<noteq> x` y by metis
          also have "... = fvs (([x \<leftrightarrow> y] \<cdot> A)[z ::= N]) - {y}"
            using fvs_simp(3) by metis
          also have "... \<subseteq> fvs ([x \<leftrightarrow> y] \<cdot> A) - {z} \<union> fvs N - {y}"
            using A by auto
          also have "... = (fvs ([x \<leftrightarrow> y] \<cdot> A) - {y}) - {z} \<union> fvs N" using `y \<notin> fvs N` by auto
          also have "... = fvs (Fn x T A) - {z} \<union> fvs N"
          proof(cases "x \<in> fvs A")
            case True
              have "fvs ([x \<leftrightarrow> y] \<cdot> A) - {y} = ([x \<leftrightarrow> y] {$} fvs A) - {y}"
                using trm_prm_fvs by metis
              also have "... = fvs A - {x} \<union> {y} - {y}"
                using prm_set_unit_action `y \<notin> fvs A` `x \<in> fvs A` by metis
              also have "... = fvs A - {x}" using `y \<notin> fvs A` by auto
              also have "... = fvs (Fn x T A)" using fvs_simp(3) by metis
              finally have "fvs ([x \<leftrightarrow> y] \<cdot> A) - {y} = fvs (Fn x T A)".
              thus ?thesis by auto
            next
            case False
              consider "x = y" | "x \<noteq> y" by auto
              hence "fvs (Fn x T A) = fvs ([x \<leftrightarrow> y] \<cdot> A) - {y}"
              proof(cases)
                case 1
                  thus ?thesis using prm_unit_equal_id trm_prm_id fvs_simp(3) by metis
                next
                case 2
                  hence "Fn x T A = Fn y T ([x \<leftrightarrow> y] \<cdot> A)"
                    using fn_eq `y \<notin> fvs A` prm_unit_commutes by metis
                  thus ?thesis using fvs_simp(3) by metis
                next
              qed
              thus ?thesis by auto
            next
          qed
          finally show ?thesis using M by metis
        next
      qed
    next
  qed
qed

lemma subst_prm:
  shows "(\<pi> \<cdot> (A[z ::= N])) = ((\<pi> \<cdot> A)[(\<pi> $ z) ::= (\<pi> \<cdot> N)])"
proof(induction A rule: trm_induct)
  case (1 x)
    consider "z = x" | "z \<noteq> x" by auto
    thus ?case proof(cases)
      case 1
        have "\<pi> \<cdot> ((Var x)[z ::= N]) = \<pi> \<cdot> N" using subst_simp(1) `z = x` by metis
        moreover have "(\<pi> \<cdot> Var x)[\<pi> $ z ::= \<pi> \<cdot> N] = \<pi> \<cdot> N"
          using `z = x` trm_prm_simp(1) subst_simp(1) by metis
        ultimately show ?thesis by metis
      next
      case 2
        hence "\<pi> $ z \<noteq> \<pi> $ x" using prm_apply_unequal by metis
        hence "(\<pi> \<cdot> Var x)[\<pi> $ z ::= \<pi> \<cdot> N] = Var (\<pi> $ x)"
          using trm_prm_simp(1) subst_simp(1) by metis
        moreover have "\<pi> \<cdot> ((Var x)[z ::= N]) = Var (\<pi> $ x)"
          using trm_prm_simp(1) subst_simp(1) `z \<noteq> x` by metis
        ultimately show ?thesis by metis
      next
    qed
  next
  case (2 A B)
    thus ?case using trm_prm_simp(2) subst_simp(2) by metis
  next
  case (3 x T A)
    consider "z = x" | "z \<noteq> x" by auto
    thus ?case proof(cases)
      case 1
        have "(\<pi> \<cdot> Fn x T A)[\<pi> $ z ::= \<pi> \<cdot> N] = Fn (\<pi> $ x) T (\<pi> \<cdot> A)"
          using `z = x` trm_prm_simp(3) subst_simp(3) by metis
        moreover have "\<pi> \<cdot> ((Fn x T A)[z ::= N]) = Fn (\<pi> $ x) T (\<pi> \<cdot> A)"
          using `z = x` trm_prm_simp(3) subst_simp(3) by metis
        ultimately show ?thesis by metis
      next
      case 2
        thus ?thesis sorry
      next
    qed
  next
qed

lemma typing_subst:
  assumes "\<Gamma>(z \<mapsto> \<tau>) \<turnstile> M : \<theta>" "\<Gamma> \<turnstile> N : \<tau>"
  shows "\<Gamma> \<turnstile> (M[z ::= N]) : \<theta>"
using assms proof(induction "depth M" arbitrary: \<Gamma> M \<theta> rule: less_induct)
  fix M :: "'a trm" and \<theta> \<Gamma>
  assume IH: "\<And>K \<Gamma> T. \<lbrakk>depth K < depth M; \<Gamma>(z \<mapsto> \<tau>) \<turnstile> K : T; \<Gamma> \<turnstile> N : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> K[z ::= N] : T"
  and "\<Gamma>(z \<mapsto> \<tau>) \<turnstile> M : \<theta>" "\<Gamma> \<turnstile> N : \<tau>"
  thus "\<Gamma> \<turnstile> M[z ::= N] : \<theta>"
  proof(induction M rule: trm_cases)
    case (1 x)
      hence M: "M = Var x" by auto
      from `\<Gamma>(z \<mapsto> \<tau>) \<turnstile> M : \<theta>` have *: "(\<Gamma>(z \<mapsto> \<tau>)) x = Some \<theta>"
        using typing_varE M by metis

      consider "x = z" | "x \<noteq> z" by auto
      thus ?case proof(cases)
        case 1
          hence "\<theta> = \<tau>" using * by auto
          moreover have "M[z ::= N] = N" using M `x = z` subst_simp(1) by auto
          ultimately show ?thesis using `\<Gamma> \<turnstile> N : \<tau>` by metis
        next
        case 2
          hence "\<Gamma> x = Some \<theta>" using * by auto
          moreover have "M[z ::= N] = M" using M `x \<noteq> z` subst_simp(1) by auto
          ultimately show ?thesis using M typing.tvar by metis
        next
      qed
    next
    case (2 A B)
      hence M: "M = App A B" by auto
      from `\<Gamma>(z \<mapsto> \<tau>) \<turnstile> M : \<theta>` obtain S
        where "\<Gamma>(z \<mapsto> \<tau>) \<turnstile> A : (TArr S \<theta>)" and "\<Gamma>(z \<mapsto> \<tau>) \<turnstile> B : S"
        using typing_appE M by metis
      moreover have "depth A < depth (App A B)" and "depth B < depth (App A B)"
        by((transfer, auto)+)
      
      ultimately have "\<Gamma> \<turnstile> A[z ::= N] : (TArr S \<theta>)" and "\<Gamma> \<turnstile> B[z ::= N] : S"
        using IH `\<Gamma> \<turnstile> N : \<tau>` M by metis+
      thus ?thesis using M subst_simp(2) typing.tapp by metis
    next
    case (3 x T A)
      hence M: "M = Fn x T A" by auto
      from `\<Gamma>(z \<mapsto> \<tau>) \<turnstile> M: \<theta>` and M obtain S
        where "\<theta> = (TArr T S)" and *: "\<Gamma>(z \<mapsto> \<tau>)(x \<mapsto> T) \<turnstile> A : S"
        using typing_fnE by metis
  
      consider "z = x" | "z \<noteq> x" by auto
      thus ?case proof(cases)
        case 1
          hence "\<Gamma>(x \<mapsto> T) \<turnstile> A : S" using * by auto
          hence "\<Gamma> \<turnstile> Fn x T A : \<theta>" using `\<theta> = (TArr T S)` typing.tfn by metis
          moreover have "(Fn x T A)[z ::= N] = Fn x T A" using subst_simp(3) `z = x` by simp
          ultimately show ?thesis using M by metis
        next
        case 2
          obtain y where y: "y = fresh_in ({z} \<union> fvs A \<union> fvs N)" by auto
          have "finite ({z} \<union> fvs A \<union> fvs N)" using fvs_finite by auto
          hence "y \<notin> ({z} \<union> fvs A \<union> fvs N)"
            using y fresh_axioms unfolding class.fresh_def by metis
          hence "y \<noteq> z" and "y \<notin> fvs A" and "y \<notin> fvs N" by auto

          have "depth ([x \<leftrightarrow> y] \<cdot> A) = depth A" using depth_prm by metis
          hence 1: "depth ([x \<leftrightarrow> y] \<cdot> A) < depth (Fn x T A)" by(transfer', auto)

          from `y \<notin> fvs A` have "\<Gamma>(z \<mapsto> \<tau>)(y \<mapsto> T) \<turnstile> [x \<leftrightarrow> y] \<cdot> A : S"
            using * typing_swp by metis
          hence 2: "\<Gamma>(y \<mapsto> T)(z \<mapsto> \<tau>) \<turnstile> [x \<leftrightarrow> y] \<cdot> A : S"
            using fun_upd_twist `y \<noteq> z` by metis

          have 3: "\<Gamma>(y \<mapsto> T) \<turnstile> N : \<tau>" using `y \<notin> fvs N` `\<Gamma> \<turnstile> N : \<tau>` typing_weaken by metis

          have "\<Gamma>(y \<mapsto> T) \<turnstile> (([x \<leftrightarrow> y] \<cdot> A)[z ::= N]) : S" using 1 2 3 IH M by metis
          hence "\<Gamma> \<turnstile> Fn y T (([x \<leftrightarrow> y] \<cdot> A)[z ::= N]) : \<theta>"
            using typing.tfn `\<theta> = (TArr T S)` by metis
          moreover have "(Fn x T A)[z ::= N] = Fn y T (([x \<leftrightarrow> y] \<cdot> A)[z ::= N])"
            using subst_simp(3) y `z \<noteq> x` by metis
          ultimately show ?thesis using M by metis
        next
      qed
    next
  qed
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
    thus ?case
      using fvs_simp(2) Un_assoc Un_left_commute subset_Un_eq sup.right_idem
      by metis
  next
  case (app2 B B' A)
    thus ?case
      using fvs_simp(2) Un_assoc Un_left_absorb subset_Un_eq
      by metis
  next
  case (fn A A' x T)
    thus ?case
      using fvs_simp(3) DiffD2 DiffI Diff_subset subset_iff
      by smt
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
using assms by(cases, auto simp add: trm_distinct)

lemma beta_reduction_left_appE:
  assumes "(App A B) \<rightarrow>\<beta> M'"
  shows "
    (\<exists>x T X. A = (Fn x T X) \<and> M' = (X[x ::= B])) \<or>
    (\<exists>A'. (A \<rightarrow>\<beta> A') \<and> M' = App A' B) \<or>
    (\<exists>B'. (B \<rightarrow>\<beta> B') \<and> M' = App A B')
  "
using assms by(
  cases,
  metis trm_simp(2) trm_simp(3),
  metis trm_simp(2) trm_simp(3),
  metis trm_simp(2) trm_simp(3),
  metis trm_distinct(6)
)

lemma beta_reduction_left_fnE:
  assumes "(Fn x T A) \<rightarrow>\<beta> M'"
  shows "\<exists>A'. (A \<rightarrow>\<beta> A') \<and> M' = (Fn x T A')"
using assms proof(cases, metis trm_distinct(6), metis trm_distinct(6), metis trm_distinct(6))
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

theorem preservation:
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

inductive is_value :: "'a trm \<Rightarrow> bool" where
  var: "is_value (Var x)"
| app_var: "is_value B \<Longrightarrow> is_value (App (Var x) B)"
| app_app: "\<lbrakk>is_value (App C D); is_value B\<rbrakk> \<Longrightarrow> is_value (App (App C D) B)"
| fn:  "is_value A \<Longrightarrow> is_value (Fn x T A)"

theorem progress:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
  shows "is_value M \<or> (\<exists>M'. (M \<rightarrow>\<beta> M'))"
using assms proof(induction M arbitrary: \<Gamma> \<tau> rule: trm_induct)
  case (1 x)
    thus ?case using is_value.var by metis
  next
  case (2 A B)
    from `\<Gamma> \<turnstile> App A B : \<tau>` obtain \<sigma>
      where "\<Gamma> \<turnstile> A : (TArr \<sigma> \<tau>)" and "\<Gamma> \<turnstile> B : \<sigma>"
      using typing_appE by metis
    hence A: "is_value A \<or> (\<exists>A'. (A \<rightarrow>\<beta> A'))" and B: "is_value B \<or> (\<exists>B'. (B \<rightarrow>\<beta> B'))"
      using "2.IH" by auto

    consider "is_value B" | "\<exists>B'. (B \<rightarrow>\<beta> B')" using B by auto
    thus ?case proof(cases)
      case 1
        consider "is_value A" | "\<exists>A'. (A \<rightarrow>\<beta> A')" using A by auto
        thus ?thesis proof(cases)
          case 1
            thus ?thesis proof(induction A rule: trm_cases)
              case (1 x)
                thus ?thesis using `is_value B` is_value.app_var by metis
              next
              case (2 C D)
                thus ?thesis using `is_value B` is_value.app_app by metis
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
    from `\<Gamma>(x \<mapsto> T) \<turnstile> A : \<sigma>` consider "is_value A" | "\<exists>A'. (A \<rightarrow>\<beta> A')"
      using "3.IH" by metis

    thus ?case proof(cases)
      case 1
        thus ?thesis using is_value.fn by metis
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

lemma progress':
  assumes "M \<rightarrow>\<beta>\<^sup>* M'" "\<Gamma> \<turnstile> M : \<tau>"
  shows "\<Gamma> \<turnstile> M' : \<tau>"
using assms proof(induction)
  case (reflexive M)
    thus ?case.
  next
  case (transitive M M' M'')
    thus ?case using preservation by metis
  next
qed

theorem safety:
  assumes "M \<rightarrow>\<beta>\<^sup>* M'" "\<Gamma> \<turnstile> M : \<tau>"
  shows "is_value M' \<or> (\<exists>M''. (M' \<rightarrow>\<beta> M''))"
using assms proof(induction)
  case (reflexive M)
    thus ?case using progress by metis
  next
  case (transitive M M' M'')
    hence "\<Gamma> \<turnstile> M' : \<tau>" using progress' by metis
    hence "\<Gamma> \<turnstile> M'' : \<tau>" using preservation `M' \<rightarrow>\<beta> M''` by metis
    thus ?case using progress by metis
  next
qed

end
end